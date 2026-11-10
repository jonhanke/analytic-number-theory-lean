# H. Davenport, *Multiplicative Number Theory* (2nd ed., revised by H. L. Montgomery, 1980): map to the Lean library

Each row is a result of the book, the Lean declarations that formalize it, and its status, computed from the Lean kernel (an audit of the axioms and hypotheses of every declaration): *proved* means proved with only the standard axioms and no unproved input; *proved in part* that a part, a special case or one instance is proved; *proved, conditional* that an unproved input (a named statement) is assumed; *refuted as stated in the book* that the library proves the printed statement false and proves a corrected form (see the errata in the README); *in Mathlib* that Mathlib (a dependency) has the result and the Lean name is Mathlib's. Results that are only in Tau Ceti or PrimeNumberTheoremAnd (which this library does not depend on) are marked so. The statements in the third column are short descriptions, not quotations; read the book for the exact wording. The column *Also in* credits other libraries: Mathlib, Tau Ceti or PrimeNumberTheoremAnd declarations that prove the result, a part of it, or a closely related statement (as recorded by the coverage audit). Davenport numbers neither his results nor his formulas consistently, so the items are numbered *chapter-k*, the k-th result of the chapter (he calls his chapters sections) in the order of the text. Pages are pages of the pdf file (the book page is the pdf page minus 10).

Rows: 432. proved: 163; not formalized: 90; in Mathlib: 80; proved in part: 45; partly in other libraries; not proved here: 36; in Tau Ceti only (not a dependency): 8; in PrimeNumberTheoremAnd only (not a dependency): 7; proved, conditional: 3. Proved here and also in another library: 59.


## Chapter 1: Primes in Arithmetic Progression (book pp. 1-11; pdf pp. 11-21)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 1-1 | 11-12 | Euler product: zeta(s) equals the product over primes of (1 - p^-s)^-1 for s > 1 (analytic form of unique factorization) | `riemannZeta_eulerProduct_tprod` | in Mathlib |  |
| 1-2 | 12 | log zeta(s) = sum over primes p and m >= 1 of p^(-ms)/m for s > 1 | `riemannZeta_eulerProduct_exp_log`, `log_riemannZeta_eq`, `DirichletCharacter.eulerProduct_log_eq_LSeries`, `NTKB.Davenport.logL`, `NTKB.Davenport.exp_logL`, `NTKB.Davenport.sum_inv_mul_logL` | in Mathlib |  |
| 1-3 | 12 | sum of 1/p over primes diverges (hence infinitely many primes), obtained from zeta(s) -> infinity as s -> 1+ | `Nat.Primes.not_summable_one_div` | in Mathlib |  |
| 1-4 | 12-13 | Dirichlet characters mod a prime q: chi_w(n) = w^index(n) with w^(q-1) = 1, zero on multiples of q, periodic, completely multiplicative, q-1 of them | `DirichletCharacter`, `DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity` | in Mathlib |  |
| 1-5 | 13 | orthogonality: sum over w of w^(-index(a)) w^(index(n)) is q-1 if n = a mod q and 0 otherwise | `DirichletCharacter.sum_char_inv_mul_char_eq` | in Mathlib |  |
| 1-6 | 13 | L_w(s) = sum w^index(n) n^-s has an Euler product and is nonzero for s > 1 | `DirichletCharacter.LSeries_eulerProduct_tprod`, `DirichletCharacter.LFunction_ne_zero_of_one_le_re` | in Mathlib |  |
| 1-7 | 13-14 | log L_w(s) = sum over p, m of w^(index(p^m)) p^(-ms)/m, the series branch being the natural logarithm | `DirichletCharacter.eulerProduct_log_eq_LSeries`, `DirichletCharacter.LSeries_eq_exp_LSeries` | in Mathlib |  |
| 1-8 | 14 | key identity (A): (1/(q-1)) sum_w conj(w)^index(a) log L_w(s) = sum over p^m = a mod q of p^(-ms)/m = sum over p = a of p^-s + O(1) | `NTKB.Davenport.logL`, `NTKB.Davenport.exp_logL`, `NTKB.Davenport.sum_inv_mul_logL` | proved | Mathlib: `ArithmeticFunction.vonMangoldt.residueClass_apply`, Mathlib: `ArithmeticFunction.vonMangoldt.LSeries_residueClass_eq` |
| 1-9 | 14 | goal: left side of (A) tends to +infinity as s -> 1+, giving infinitely many primes p = a mod q | `Nat.infinite_setOfPred_prime_and_eq_mod`, `Nat.forall_exists_prime_gt_and_eq_mod`, `Nat.forall_exists_prime_gt_and_modEq` | in Mathlib |  |
| 1-10 | 14 | the series of p^-s over primes p = a mod q diverges as s -> 1+, i.e. sum of 1/p over p = a mod q diverges | `NTKB.Davenport.tendsto_sum_prime_rpow_atTop`, `NTKB.Davenport.not_summable_one_div_prime` | proved | Tau Ceti: `NumberField.Chebotarev.hasDirichletDensity_primesCongruent` |
| 1-11 | 14 | L_1(s) = (1 - q^-s) zeta(s) tends to +infinity as s -> 1+ | `DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta`, `DirichletCharacter.LFunctionTrivChar_residue_one` | in Mathlib |  |
| 1-12 | 14-15 | for w not 1 the series L_w(s) converges for s > 0 (Dirichlet's test, bounded partial sums) uniformly on s >= delta, so L_w continuous; the problem reduces to B: L_w(1) nonzero | `NTKB.Davenport.tendsto_dirichletPartialSum_LFunction`, `NTKB.Davenport.tendsto_sum_char_div_LFunction` | proved in part | Mathlib: `Monotone.cauchySeq_series_mul_of_tendsto_zero_of_bounded`, Mathlib: `Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded`, Mathlib: `DirichletCharacter.differentiable_LFunction` |
| 1-13 | 15 | inequality (C): product over all w of L_w(s) is at least 1 for s > 1 (take a = 1 in (A)) | `NTKB.Davenport.one_le_prod_LFunction` | proved |  |
| 1-14 | 15-16 | for complex w, L_w(1) is nonzero (a zero at w and conj w would beat the simple pole of L_1 in (C)) | `DirichletCharacter.LFunction_apply_one_ne_zero` | in Mathlib |  |
| 1-15 | 16-17 | real case w = -1 (Legendre symbol): L(1) = sum (n/q)/n is nonzero; L(1) >= 0 by continuity | `DirichletCharacter.LFunction_apply_one_ne_zero`, `DirichletCharacter.LFunction_ne_zero_of_re_eq_one` | in Mathlib |  |
| 1-16 | 17 | for the quadratic Gauss sum G(n) = sum_m (m/q) e(mn/q) one has G(n) = (n/q) G(1) (E) | `gaussSum_mulShift_eq` | in Mathlib |  |
| 1-17 | 18 | -log(1 - z) = sum z^n/n, and sum e^(i n theta)/n = -log(2 sin(theta/2)) + i(pi - theta)/2 for 0 < theta < 2 pi | `NTKB.Davenport.tendsto_sum_range_pow_div`, `NTKB.Davenport.neg_log_one_sub_exp` | proved | Mathlib: `Complex.hasSum_taylorSeries_neg_log` |
| 1-18 | 18 | for q = 3 mod 4: L(1) = -(pi / q^(3/2)) sum_{m=1}^{q-1} m (m/q) (formula G) | `NTKB.Davenport.LFunction_one_legendreChar` | proved | Tau Ceti: `DirichletCharacter.two_mul_LFunction_one_eq_sum_mul_cot`, Tau Ceti: `DirichletCharacter.IsPrimitive.sum_inv_mul_pi_mul_cot` |
| 1-20 | 19 | for q = 3 mod 4 the sum of m (m/q) is an odd integer, hence nonzero, so L(1) is nonzero | `NTKB.Davenport.odd_sum_mul_legendreSym`, `NTKB.Davenport.LFunction_one_legendreChar_ne_zero` | proved |  |
| 1-21 | 19 | Dirichlet's second finite expression (8): for q = 3 mod 4, L(1) is a positive multiple of (pi/sqrt q) times the half-range sum of (m/q) over m < q/2; so residues outnumber nonresidues there | `NTKB.Davenport.LFunction_one_legendreChar_half`, `NTKB.Davenport.legendreSym_two_sub_two_mul_sum` | proved |  |
| 1-22 | 19 | for q = 1 mod 4: L(1) = -(1/sqrt q) sum (m/q) log(2 sin(pi m/q)), equivalently L(1) = -(2/sqrt q) log of Q = product of sin(pi N/q) over product of sin(pi R/q), formula (9) | `NTKB.Davenport.LFunction_one_legendreChar_of_one_mod_four` | proved |  |
| 1-23 | 20 | Gauss: product of (x - zeta^R) over residues R is (Y(x) - sqrt q Z(x))/2 and over nonresidues N is (Y(x) + sqrt q Z(x))/2 with Y, Z integer polynomials (q = 1 mod 4; proved in sec. 3) | `NTKB.Davenport.exists_gauss_product` | proved |  |
| 1-24 | 20 | consequence Y^2 - q Z^2 = 4q for integers Y = Y(1), Z = Z(1) with Z nonzero (solves the negative Pell equation for prime q = 1 mod 4) | `NTKB.Davenport.exists_sq_sub_mul_sq_eq` | proved |  |
| 1-25 | 20-21 | Q is expressed through Y and Z (Q = ratio like (Y - sqrt q Z)/(Y + sqrt q Z)) so Q not 1 because Z nonzero, completing L(1) nonzero for q = 1 mod 4 and Dirichlet's theorem for prime modulus | `NTKB.Davenport.exists_LFunction_one_eq_log`, `NTKB.Davenport.LFunction_one_legendreChar_ne_zero_of_one_mod_four` | proved |  |

## Chapter 2: Gauss' Sum (book pp. 12-16; pdf pp. 22-26)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 2-1 | 22 | for an odd prime q the square of G = sum_n (n/q) e(n/q) is q if q = 1 mod 4 and -q if q = 3 mod 4 | `gaussSum_sq` | in Mathlib |  |
| 2-2 | 22-23 | Gauss's sign theorem: G = sqrt q if q = 1 mod 4 and G = i sqrt q if q = 3 mod 4, with e(x) = exp(2 pi i x) | `NTKB.gaussSum_legendreChar` | proved | Tau Ceti: `sum_range_cexp_two_pi_I_sq_div`, Tau Ceti: `sum_comp_mul_sq` |
| 2-3 | 23 | for a primitive q-th root of unity z other than exp(2 pi i/q) the sign of the quadratic Gauss sum cannot be specified: replacing z by z^n with n a nonresidue flips it | `gaussSum_mulShift_eq` | in Mathlib |  |
| 2-4 | 23 | G = sum over x mod q of e(x^2/q), since x -> x^2 hits 0 once and each residue twice | `NTKB.gaussSum_legendreChar_eq_sum_sq` | proved | Tau Ceti: `sum_comp_mul_sq`, Tau Ceti: `sum_addChar_mul_sq` |
| 2-5 | 23 | Dirichlet 1835: S(N) = sum_{n=0}^{N-1} e(n^2/N) equals (1+i) sqrt N, sqrt N, 0, i sqrt N for N = 0,1,2,3 mod 4 respectively | `NTKB.sum_range_cexp_two_pi_I_sq_div` | proved | Tau Ceti: `sum_range_cexp_two_pi_I_sq_div` |
| 2-6 | 24 | Poisson summation: sum over A <= n <= B of f(n), with end terms halved, equals sum over v of the integral of f(x) e(vx) dx for f continuous and piecewise monotone | `Real.tsum_eq_tsum_fourier`, `Real.tsum_eq_tsum_fourier_of_rpow_decay` | partly in other libraries; not proved here |  |
| 2-7 | 24 | Dirichlet's theorem on Fourier series: for piecewise monotone f the Fourier series converges everywhere to f, or to the mean of one-sided limits at a jump | — | not formalized |  |
| 2-8 | 25 | the improper integral of e^(2 pi i y^2) over the real line converges in both the narrow and symmetric senses (second mean value theorem) | — | not formalized |  |
| 2-9 | 26 | S(N) = (1 + e^(-pi i N/2)) C sqrt N with absolute constant C, fixed by N = 1 to be C = 1/(1 - i), which yields the four values in row 2-5 | `NTKB.sum_range_cexp_two_pi_I_sq_div` | proved | Tau Ceti: `sum_range_cexp_two_pi_I_sq_div` |

## Chapter 3: Cyclotomy (book pp. 17-26; pdf pp. 27-36)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 3-1 | 27 | for an odd prime q the polynomial x^(q-1)+...+1 is irreducible over the rationals, so a primitive q-th root of unity has degree q-1 | `Polynomial.cyclotomic.irreducible_rat`, `Polynomial.cyclotomic_prime` | in Mathlib |  |
| 3-2 | 27 | the q-1 nontrivial q-th roots of unity sum to -1, so every integer polynomial in z equals a1 z + ... + a_(q-1) z^(q-1) uniquely | `NTKB.Davenport.exists_aeval_eq_sum_units`, `NTKB.Davenport.eq_of_sum_units_eq`, `NTKB.Davenport.eq_of_sum_mul_pow_eq_zero` | proved | Mathlib: `IsCyclotomicExtension.Rat.finrank` |
| 3-3 | 28 | Gaussian periods: for q-1 = e f, eta_j = sum of z^n over n in 1..q-1 with index(n) = j mod e (f terms each); periodic in j with period e | `NTKB.Davenport.gaussianPeriod`, `NTKB.Davenport.gaussianPeriod_add`, `NTKB.Davenport.sum_gaussianPeriod`, `NTKB.Davenport.gaussianPeriod_eq_sum_range` | proved |  |
| 3-4 | 28 | for e = 2 the periods are eta_0 = sum of z^R, eta_1 = sum of z^N, with eta_0 - eta_1 = G and eta_0 + eta_1 = -1, so eta = (-1 +- sqrt(q*))/2 with q* = (-1)^((q-1)/2) q | `NTKB.Davenport.gaussianPeriod_two_eq`, `NTKB.Davenport.gaussianPeriod_two_sub`, `NTKB.Davenport.gaussianPeriod_two_sub_eq_gaussSum`, `NTKB.Davenport.gaussianPeriod_two_zero_eq`, `NTKB.Davenport.gaussianPeriod_two_one_eq` | proved | Tau Ceti: `exists_mem_sq_eq_oddPrimeDiscriminant` |
| 3-5 | 28 | with z = e^(2 pi i/q), the period eta_0 is determined and equals (1/e) (sum over x mod q of e(x^e/q) minus 1) | `NTKB.Davenport.gaussianPeriod_zero_eq` | proved |  |
| 3-7 | 28-29 | lemma: if F(z) = sum A_r z^r satisfies F(z^m) = F(z) whenever index(m) = 0 mod e, then F(z) is a linear combination of the Gaussian periods eta_j with coefficients A_r (also for coefficients in Z[x]) | `NTKB.Davenport.aeval_eq_sum_gaussianPeriod` | proved |  |
| 3-8 | 29-30 | Gauss: for q = 1 mod 4 with q* = (-1)^((q-1)/2) q the products of (x - z^R) and (x - z^N) are (Y(x) -+ sqrt(q*) Z(x))/2 with Y, Z in Z[x], so Y^2 - q* Z^2 = 4 (x^(q-1)+...+1) | `NTKB.Davenport.exists_gauss_product` | proved |  |
| 3-9 | 30-31 | Gauss's theorem: if q = 2^k + 1 is prime then each q-th root of unity is expressible by rational numbers and k nested square roots, via the tower of periods of 2, 4, ..., 2^k terms | — | not formalized |  |
| 3-10 | 31 | the regular q-gon is constructible by ruler and compasses for Fermat primes q: all periods used are real because index(-1) = 2^(k-1) is divisible by each e = 2..2^(k-1); 2 cos(2 pi/q) is the 2-term period | — | not formalized |  |
| 3-11 | 31-32 | Kummer's cubic periods for q = 1 mod 3: eta_0, eta_1, eta_2 sum over cubic residues A and the two nonresidue classes B, C; eta_0 = (sum over x mod q of e(x^3/q) - 1)/3 is uniquely determined | `NTKB.Davenport.gaussianPeriod_zero_eq` | proved in part |  |
| 3-13 | 32 | cubic Gauss sum tau = sum of chi(n) e(n/q) with chi(n) = w^index(n), w a primitive cube root of unity, satisfies abs(tau) = sqrt q | `DirichletCharacter.norm_gaussSum_stdAddChar`, `gaussSum_mul_gaussSum_eq_card` | in Mathlib |  |
| 3-15 | 33 | z_j = 1 + 3 eta_j equals tau-combinations: z_0 = tau + conj tau = 2 sqrt q cos theta, z_1 and z_2 = 2 sqrt q cos(theta -+ 2 pi/3 or similar); exactly one z_j in each of three intervals | — | not formalized |  |
| 3-16 | 33 | Kummer's problem: distribution of theta(q) as q ranges over primes; conjectured 1:2:3 frequencies refuted numerically; Heath-Brown and Patterson proved theta(q) equidistributed | — | not formalized |  |
| 3-17 | 34 | tau^3 = q (A + B w) with A, B rational integers (w a cube root of unity), obtained by writing tau^2 as a Jacobi-type sum and multiplying by tau | `gaussSum_pow_eq_prod_jacobiSum`, `jacobiSum_mem_algebraAdjoin_of_pow_eq_one` | in Mathlib |  |
| 3-18 | 34-35 | q = A^2 - A B + B^2 with B divisible by 3 (via algebraic-integer congruence), hence 4q = a^2 + 27 b^2 (a = 2A - B, b = B/3) and cos(3 theta) = a/(2 sqrt q) up to the sign of a | — | partly in other libraries; not proved here |  |
| 3-19 | 35 | sign of a: a = 1 mod 3, by counting solutions of v^2 = u(u+1) mod q in two ways | — | not formalized |  |
| 3-20 | 35-36 | the three z_j are roots of z^3 - 3 q z - q a = 0 | — | not formalized |  |

## Chapter 4: Primes in Arithmetic Progression: The General Modulus (book pp. 27-34; pdf pp. 37-44)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 4-1 | 37 | Dirichlet characters mod q: periodic mod q, completely multiplicative, zero when (n,q) > 1; there are phi(q) of them | `DirichletCharacter`, `DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity` | in Mathlib |  |
| 4-2 | 37-38 | modulus p^a, p odd prime: a primitive root exists and the characters are w^index(n) with w^phi(p^a) = 1, phi(p^a) of them | `ZMod.isCyclic_units_of_prime_pow`, `ZMod.isCyclic_units_iff`, `MulChar.equiv_rootsOfUnity` | in Mathlib |  |
| 4-3 | 38 | modulus 2^a: trivial for a = 1, sign character for a = 2, and for a >= 3 every unit is uniquely (-1)^v 5^v' with v mod 2, v' mod 2^(a-2); characters w^v w'^v', 2^(a-1) of them | `ZMod.isComplement'_zpowers_unitFive_neg_one`, `ZMod.orderOf_five`, `ZMod.isCyclic_units_two_pow_iff` | in Mathlib |  |
| 4-4 | 38 | general q = prod p_i^a_i: characters mod q are products of characters mod the prime power factors, phi(q) in total | — | partly in other libraries; not proved here |  |
| 4-5 | 38-39 | the principal character chi_0 is 1 on units; characters mod q form a group isomorphic to the group of reduced residue classes, with explicit duality via exponent vectors (A) | `DirichletCharacter.mulEquiv_units`, `MulChar.mulCharEquiv` | in Mathlib |  |
| 4-6 | 40 | (B) sum over n mod q of chi(n) is phi(q) if chi is principal and 0 otherwise | `MulChar.sum_eq_zero_of_ne_one`, `MulChar.sum_one_eq_card_units` | in Mathlib |  |
| 4-7 | 40 | (C) sum over all characters chi of chi(n) is phi(q) if n = 1 mod q and 0 otherwise | `DirichletCharacter.sum_characters_eq`, `DirichletCharacter.sum_characters_eq_zero` | in Mathlib |  |
| 4-9 | 40 | any nonzero function on integers that is periodic mod q, multiplicative and zero when (n,q) > 1 is one of the phi(q) characters (proved via (C)) | `DirichletCharacter` | in Mathlib |  |
| 4-10 | 41 | (D) selecting a residue class: (1/phi(q)) sum over chi of conj(chi(a)) chi(n) is 1 if n = a mod q and 0 otherwise, for (a,q) = 1 | `DirichletCharacter.sum_char_inv_mul_char_eq` | in Mathlib |  |
| 4-11 | 41 | L(s,chi) = sum chi(n) n^-s for s > 1 has Euler product over primes of (1 - chi(p) p^-s)^-1 | `DirichletCharacter.LSeries_eulerProduct_tprod`, `DirichletCharacter.LSeries_eulerProduct_hasProd`, `DirichletCharacter.LSeries_eulerProduct` | in Mathlib |  |
| 4-12 | 41 | L(s,chi) is nonzero for s > 1 | `DirichletCharacter.LFunction_ne_zero_of_one_le_re` | in Mathlib |  |
| 4-13 | 41 | log L(s,chi) = sum over p, m of chi(p^m) p^(-ms)/m | `DirichletCharacter.eulerProduct_log_eq_LSeries`, `DirichletCharacter.LSeries_eq_exp_LSeries` | in Mathlib |  |
| 4-14 | 41 | (E) (1/phi(q)) sum_chi conj(chi(a)) log L(s,chi) = sum over p^m = a mod q of p^(-ms)/m = sum over p = a mod q of p^-s + O(1) | `NTKB.Davenport.logL`, `NTKB.Davenport.exp_logL`, `NTKB.Davenport.sum_inv_mul_logL` | proved | Mathlib: `ArithmeticFunction.vonMangoldt.residueClass_apply`, Mathlib: `ArithmeticFunction.vonMangoldt.LSeries_residueClass_eq` |
| 4-15 | 41 | (F) L(s,chi_0) = zeta(s) times product over p dividing q of (1 - p^-s), so log L(s,chi_0) -> +infinity as s -> 1+ | `DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta` | in Mathlib |  |
| 4-16 | 42 | for nonprincipal chi it suffices to prove L(1,chi) nonzero; for complex chi the product over all characters is at least 1 (as in sec. 1) so L(1,chi) is nonzero | `DirichletCharacter.LFunction_apply_one_ne_zero` | in Mathlib |  |
| 4-17 | 42 | for real nonprincipal chi, L(1,chi) nonzero (Dirichlet used the class number formula; a complex-analytic proof of de la Vallee Poussin follows) | `DirichletCharacter.LFunction_apply_one_ne_zero`, `DirichletCharacter.LFunction_ne_zero_of_re_eq_one` | in Mathlib |  |
| 4-18 | 42-43 | (G) zeta(s) = 1/(s-1) + 1 - s times the integral over x >= 1 of fractional-part(x) x^(-s-1) dx for Re s > 0, so zeta is meromorphic there with simple pole residue 1 | `differentiableAt_riemannZeta`, `riemannZeta_eq_zetaAbelContinuationFormula` | partly in other libraries; not proved here |  |
| 4-19 | 43 | L(s,chi_0) is meromorphic for Re s > 0 with a simple pole at s = 1 with residue product over p dividing q of (1 - 1/p) = phi(q)/q | `DirichletCharacter.LFunctionTrivChar_residue_one` | in Mathlib |  |
| 4-20 | 43 | for chi not principal, with S(x) = sum of chi(n) for n <= x bounded, L(s,chi) = s times the integral of S(x) x^(-s-1), giving a regular function for Re s > 0 | `DirichletCharacter.differentiable_LFunction` | in Mathlib |  |
| 4-21 | 43-44 | de la Vallee Poussin: if chi real nonprincipal had L(1,chi) = 0, then psi(s) = L(s,chi) L(s,chi_0)/L(2s,chi_0) is regular for Re s > 1/2, equals a Dirichlet series with nonnegative coefficients and a_1 = 1, but psi(s) -> 0 as s -> 1/2+, contradicting the Taylor expansion about s = 2 (Landau) | — | not formalized |  |
| 4-22 | 44 | Dirichlet's theorem: infinitely many primes p = a mod q for (a,q) = 1 | `Nat.infinite_setOfPred_prime_and_eq_mod`, `Nat.forall_exists_prime_gt_and_modEq`, `Nat.frequently_atTop_prime_and_modEq` | in Mathlib |  |
| 4-23 | 44 | and the series of 1/p over primes p = a mod q diverges | `NTKB.Davenport.tendsto_sum_prime_rpow_atTop`, `NTKB.Davenport.not_summable_one_div_prime` | proved | Tau Ceti: `NumberField.Chebotarev.hasDirichletDensity_primesCongruent` |

## Chapter 5: Primitive Characters (book pp. 35-42; pdf pp. 45-52)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 5-1 | 45 | a nonprincipal character chi mod q is imprimitive if on integers coprime to q it has a period smaller than q, otherwise primitive (the principal character is left unclassified) | `DirichletCharacter.IsPrimitive`, `DirichletCharacter.conductor`, `DirichletCharacter.FactorsThrough` | in Mathlib |  |
| 5-2 | 45 | the least period q_1 of an imprimitive nonprincipal chi divides q and exceeds 1 | `DirichletCharacter.conductor_dvd_level`, `DirichletCharacter.eq_one_iff_conductor_eq_one` | in Mathlib |  |
| 5-3 | 45-46 | an imprimitive chi mod q is induced by a primitive chi_1 mod q_1: chi(n) = chi_1(n) if (n,q) = 1 and 0 otherwise, where chi_1 is extended to n coprime to q_1 by chi(n + t q_1) | `DirichletCharacter.primitiveCharacter`, `DirichletCharacter.changeLevel_primitiveCharacter`, `DirichletCharacter.primitiveCharacter_isPrimitive`, `DirichletCharacter.primitiveCharacter_apply_of_isCoprime` | in Mathlib |  |
| 5-5 | 46 | chi mod q = p1^a1 ... is primitive iff each prime-power component character is primitive; if imprimitive, q_1 is the product of the conductors of the nonprincipal components | `DirichletCharacter.conductor_prod_of_pairwise_coprime` | partly in other libraries; not proved here |  |
| 5-6 | 47 | in the exponent parametrization of characters (A of sec. 4), chi is primitive iff each m_i is coprime to p_i (modified for the 2-part) | — | not formalized |  |
| 5-7 | 47 | (C) L(s,chi) = L(s,chi_1) times product over p dividing q of (1 - chi_1(p) p^-s), valid for Re s > 1 then everywhere; in particular L(1,chi_1) nonzero implies L(1,chi) nonzero | `DirichletCharacter.LFunction_changeLevel`, `DirichletCharacter.LSeries_changeLevel` | in Mathlib |  |
| 5-8 | 47-48 | real primitive characters mod prime powers: only p odd (Legendre symbol), 4 (the nonprincipal character chi_4) and 8 (chi_8 and chi_4 chi_8); no others (a > 1 for odd p forces imprimitivity; a >= 4 for p = 2 too) | `NTKB.Davenport.eq_one_of_isPrimitive_of_isQuadratic_odd`, `NTKB.Davenport.eq_legendreChar_of_isQuadratic`, `NTKB.Davenport.two_or_three_of_isPrimitive_of_isQuadratic_two_pow`, `NTKB.Davenport.eq_chi4_of_isPrimitive`, `NTKB.Davenport.eq_chi8_or_eq_chi8'_of_isPrimitive` | proved | Mathlib: `ZMod.χ₄`, Mathlib: `ZMod.χ₈`, Mathlib: `ZMod.χ₈'`, Mathlib: `ZMod.χ₈'_eq_χ₄_mul_χ₈` |
| 5-9 | 48 | a real primitive character mod q exists iff q is a product of pairwise coprime basic moduli p (odd prime), 4, 8; it is then the product of the basic characters; there are two iff 8 divides q | `isPrimitive_fundamentalDiscriminantChar`, `Int.IsFundamentalDiscr.exists_finset_primeDiscriminant` | partly in other libraries; not proved here |  |
| 5-10 | 49 | (7) for odd n > 0: chi_4(n) = (-1/n), chi_8(n) = (2/n), chi_4(n) chi_8(n) = (-2/n) as Jacobi symbols | `jacobiSym.at_neg_one`, `jacobiSym.at_two`, `jacobiSym.at_neg_two`, `ZMod.χ₄`, `ZMod.χ₈`, `ZMod.χ₈'` | in Mathlib |  |
| 5-11 | 49 | (8) quadratic reciprocity in the form (p*/n) = (n/p) for odd prime p with p* = (-1)^((p-1)/2) p, n odd positive; more generally for squarefree odd P | `jacobiSym.quadratic_reciprocity`, `jacobiSym.quadratic_reciprocity_one_mod_four`, `jacobiSym.quadratic_reciprocity_three_mod_four`, `legendreSym.quadratic_reciprocity` | in Mathlib |  |
| 5-12 | 49 | Kronecker's extension of the Legendre-Jacobi symbol to all n (even n, negative d), under which (8) holds for every n | `NTKB.kroneckerChar_apply_odd` | proved in part | Tau Ceti: `kroneckerSym_eq_jacobiSym`, Tau Ceti: `primeDiscriminantCharFun_eq_kroneckerSym` |
| 5-13 | 49-50 | list of basic characters (-4/n), (8/n), (-8/n), (p*/n) with modulus abs(d); multiplicativity (d1 d2/n) = (d1/n)(d2/n) for coprime d1, d2 | `NTKB.Davenport.kroneckerChar_mul_apply` | proved in part | Tau Ceti: `kroneckerSym_mul_left`, Tau Ceti: `primeDiscriminantCharFun_neg_four`, Tau Ceti: `primeDiscriminantCharFun_eight`, Tau Ceti: `primeDiscriminantCharFun_neg_eight` |
| 5-14 | 50 | the real primitive characters are exactly the symbols (d/n) with d a product of coprime factors from -4, 8, -8, p*; the symbol is primitive of modulus abs(d) | `NTKB.kroneckerChar_isPrimitive` | proved in part | Tau Ceti: `isPrimitive_fundamentalDiscriminantChar`, Tau Ceti: `fundamentalDiscriminantChar_intCast` |
| 5-15 | 50 | such d are exactly the fundamental discriminants: squarefree d = 1 mod 4, or d = 4N with N squarefree, N = 2 or 3 mod 4; these are the discriminants of quadratic fields | `Int.isFundamentalDiscr_iff_squarefree` | partly in other libraries; not proved here |  |
| 5-16 | 50 | integral basis of Q(sqrt N) is (1, sqrt N) for N = 2, 3 mod 4 and (1, (1+sqrt N)/2) for N = 1 mod 4, giving discriminants 4N and N | `adjoin_halfGen_eq_top_of_mod_four_eq_one`, `adjoin_gen_eq_top_of_mod_four_ne_one`, `discr_eq_of_squarefree_of_mod_four_eq_one`, `discr_eq_four_mul_of_mod_four_ne_one` | in Tau Ceti only (not a dependency) |  |
| 5-17 | 51 | discriminants of binary quadratic forms ax^2+bxy+cy^2 are b^2 - 4ac, nonsquare, 0 or 1 mod 4; fundamental discriminants (all forms primitive) are exactly the d above | `NTKB.Davenport.isFundamentalDiscriminant_iff_forall_primitive` | proved |  |
| 5-18 | 51 | the value (d/p) controls splitting: p inert if -1, p splits into two prime ideals if +1, and p is represented by a form of discriminant d only if (d/p) is not -1 | `ncard_primesOver_quadratic_iff`, `ncard_primesOver_eq_one_or_eq_two` | partly in other libraries; not proved here |  |
| 5-19 | 51 | for a real primitive chi = (d/n): chi(-1) = +1 if d > 0 and -1 if d < 0 (checked on basic characters by multiplicativity), so chi is attached to a real or an imaginary quadratic field | `NTKB.kroneckerChar_neg_one` | proved | Tau Ceti: `fundamentalDiscriminantChar_neg_one` |
| 5-20 | 52 | for real primitive chi = (d/n): L(s,chi) = product over p of (1 - (d/p) p^-s)^-1 = sum (d/n) n^-s for Re s > 1 | `fundamentalDiscriminantChar_natCast_eq_legendreSym` | partly in other libraries; not proved here |  |

## Chapter 6: Dirichlet's Class Number Formula (book pp. 43-53; pdf pp. 53-63)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 6-1 | 53-54 | binary quadratic forms of discriminant d are grouped into classes under unimodular substitutions; every class contains a form with abs(b) <= abs(a) <= sqrt of a multiple of abs(d) (Lagrange), so the number of classes is finite | `NTKB.Davenport.exists_formEquiv_reduced`, `NTKB.Davenport.three_mul_sq_le_of_reduced`, `NTKB.Davenport.exists_finset_formEquiv` | proved | Tau Ceti: `exists_smul_isLagrangeReduced`, Tau Ceti: `IsLagrangeReduced.three_mul_abs_a_mul_abs_c_le_abs_discrim`, Tau Ceti: `finite_orbitRel_quotient_of_forall_discrim_eq` |
| 6-2 | 54 | h(d) = number of classes of forms of fundamental discriminant d (positive definite if d < 0, equivalent to a > 0 if d > 0); the principal form exists so h(d) >= 1 | `classNumber_eq_card_primitiveReducedForms` | partly in other libraries; not proved here |  |
| 6-3 | 54-55 | automorphs: only +-identity if d < 0, except d = -3 (6 automorphs) and d = -4 (4); w = number of automorphs = number of roots of unity in the field, w = 2 for d < -4 | `card_units_neg_three`, `card_units_neg_four`, `units_eq_one_or_neg_one_of_neg`, `torsionOrder_eq_of_finrank_eq_two` | in Tau Ceti only (not a dependency) |  |
| 6-4 | 55 | for d > 0 automorphs correspond to solutions of Pell's equation t^2 - d u^2 = 4; there are infinitely many, all given by (t + u sqrt d)/2 = +- (fundamental solution)^n | `Pell.exists_of_not_isSquare`, `infinite_normOneUnits_of_pos_of_not_isSquare` | partly in other libraries; not proved here |  |
| 6-5 | 55-56 | explicit automorph for a solution (t,u): alpha = (t - b u)/2, beta = -c u, gamma = a u, delta = (t + b u)/2 (E), acting on x - theta y by multiplication by (t - u sqrt d)/2 | `NTKB.Davenport.formSubst_automorph` | proved in part | Tau Ceti: `map_stabilizerEquivNormOneUnits_symm_apply` |
| 6-6 | 56-57 | primary representations (d > 0): from each automorph orbit of representations of n choose the one with x - theta y > 0 and ratio (x - theta' y)/(x - theta y) in a fixed interval of length 2 log epsilon (10, 11); their number R(n) is finite | — | not formalized |  |
| 6-7 | 57 | basic theorem: for n > 0 with (n,d) = 1, R(n) = w times the sum over m dividing n of (d/m), where w = 1 for d > 0 (A2, Landau Satz 204) | `dedekindZetaCoeff_eq_sum_divisors` | partly in other libraries; not proved here |  |
| 6-8 | 57-58 | average of R(n): the mean over n <= N with (n,d) = 1 tends to w (phi(abs d)/abs d) L(1,chi), chi(m) = (d/m) (A3) | — | not formalized |  |
| 6-9 | 58-59 | for d < 0 the lattice point count in the ellipse a x^2 + b x y + c y^2 < N with congruence conditions gives mean value of R(n,f) equal to 2 pi/sqrt(abs d) times phi(abs d)/abs d, independent of f | — | not formalized |  |
| 6-10 | 59 | (15) for d < 0: h(d) = (w sqrt(abs d)/(2 pi)) L(1,chi) | `classNumber_eq_card_units_mul_LFunction_one`, `classNumber_eq_LFunction_one_of_discr_ne` | in Tau Ceti only (not a dependency) |  |
| 6-11 | 59-60 | for d > 0 the lattice point count in a hyperbolic sector between two lines gives area (N/a) log epsilon, with epsilon = (t0 + u0 sqrt d)/2 fundamental | — | not formalized |  |
| 6-12 | 60 | (16) for d > 0: h(d) = (sqrt d/log epsilon) L(1,chi) | — | partly in other libraries; not proved here |  |
| 6-13 | 60 | consequence of (15) and (16): L(1,chi) > 0 for real primitive chi since h(d) >= 1 | `NTKB.Davenport.LFunction_one_pos_of_isQuadratic` | proved | Tau Ceti: `DirichletCharacter.LFunction_apply_one_pos`, Tau Ceti: `DirichletCharacter.LFunction_pos_of_one_le`, Tau Ceti: `fundamentalDiscriminantCharCast_LFunction_pos` |
| 6-14 | 60 | Gauss sum of a real primitive character: tau(chi) = sum_{n=1}^{abs d} chi(n) e(n/abs d) equals sqrt d for d > 0 and i sqrt(abs d) for d < 0 (quoted from Landau Satz 215) | `NTKB.gaussSum_kroneckerChar` | proved | Mathlib: `DirichletCharacter.norm_gaussSum_stdAddChar`, Mathlib: `gaussSum_sq` |
| 6-15 | 60 | (17) for d < 0: L(1,chi) = -(pi/abs(d)^(3/2)) sum_{m=1}^{abs d} m (d/m) | `NTKB.Davenport.LFunction_one_kroneckerChar_of_neg` | proved | Tau Ceti: `DirichletCharacter.two_mul_LFunction_one_eq_sum_mul_cot`, Tau Ceti: `DirichletCharacter.IsPrimitive.sum_inv_mul_pi_mul_cot` |
| 6-16 | 60-61 | (18) for d > 0: L(1,chi) = -(1/sqrt d) sum_{m=1}^{d-1} (d/m) log sin(pi m/d) | `NTKB.Davenport.LFunction_one_kroneckerChar_of_pos` | proved |  |
| 6-17 | 61 | Jacobi's formula (19) for d = -q, q = 3 mod 4 prime greater than 3: h(-q) = -(1/q) sum_{m=1}^{q-1} m (m/q) | — | not formalized |  |
| 6-18 | 61 | the number H on the right of (19) is an integer: by Euler's criterion sum m (m/q) is congruent to sum m^((q+1)/2), which is 0 mod q | `NTKB.Davenport.dvd_sum_mul_legendreSym`, `NTKB.Davenport.exists_pos_int_sum_mul_legendreSym` | proved |  |
| 6-20 | 61-62 | for an integral ideal a of a quadratic field K with basis alpha, beta, the form N(alpha x + beta y)/N a = a x^2 + b x y + c y^2 has integer coefficients and discriminant d; its class is independent of basis and of the ideal class in the narrow sense | `exists_pos_primitive_form_invertibleFractionalIdeal_eq` | partly in other libraries; not proved here |  |
| 6-21 | 62 | ideals a, b are equivalent in the narrow sense if a = (lambda) b for some lambda in K with norm N(lambda) > 0 (lambda not required integral) | `NarrowClassGroup` | in Tau Ceti only (not a dependency) |  |
| 6-22 | 62 | one-to-one correspondence between a set of representative forms of discriminant d (positive definite if d < 0) and classes of ideals under narrow equivalence | — | in Tau Ceti only (not a dependency) |  |
| 6-23 | 62 | class numbers: h(d) = h_1(d) if d < 0 or if d > 0 and a unit of norm -1 exists; h(d) = 2 h_1(d) if d > 0 and no unit of norm -1 exists (h_1 = class number of the field) | `card_eq_card_classGroup_iff_exists_norm_eq_neg_one`, `card_eq_two_mul_card_classGroup_of_forall_norm_ne_neg_one` | in Tau Ceti only (not a dependency) |  |
| 6-24 | 62 | automorphs for d > 0 correspond to units of norm +1; epsilon = epsilon_1 if N epsilon_1 = +1 and epsilon = epsilon_1^2 if N epsilon_1 = -1, hence h(d) log epsilon = 2 h_1(d) log epsilon_1 | — | partly in other libraries; not proved here |  |
| 6-25 | 62-63 | class number of a quadratic field: h_1(d) = -(w/(2 abs d)) sum m (d/m) for d < 0; h_1(d) log epsilon_1 = (sqrt d / 2) L(1,chi) = -(1/2) sum (d/m) log sin(pi m/d) for d > 0 | `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` | partly in other libraries; not proved here |  |
| 6-26 | 63 | general class number formula (Hecke Satz 125): for a number field K, h times regulator is expressed through the residue at s = 1 of the Dedekind zeta function | `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`, `NumberField.dedekindZeta_residue_def`, `NumberField.dedekindZeta_residue_pos` | in Mathlib |  |
| 6-27 | 63 | for a quadratic field zeta_K(s) = zeta(s) L(s,chi) so the residue is L(1,chi); class number formulas become (15), (16) | `dedekindZeta_eq_riemannZeta_mul_LFunction`, `dedekindZeta_residue_eq_LFunction_one`, `dedekindZetaC_eq_riemannZeta_mul_LFunction` | in Tau Ceti only (not a dependency) |  |

## Chapter 7: The Distribution of the Primes (book pp. 54-58; pdf pp. 64-68)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 7-2 | 65 | Asymptotic expansion li x = x/log x + x/(log x)^2 + ... obtained by repeated integration by parts | `TauCeti.Real.logIntegral`, `TauCeti.Real.logIntegral_eq_div_log_sub_add`, `TauCeti.Real.logIntegral_isEquivalent_div_log` | partly in other libraries; not proved here |  |
| 7-3 | 65 | Tchebychev 1851: liminf pi(x)/li x <= 1 <= limsup pi(x)/li x, and li x is the only function of that expansion type approximating pi | — | not formalized |  |
| 7-4 | 65 | Definition of the von Mangoldt function Lambda(n) = log p for n a power of prime p, else 0 | `ArithmeticFunction.vonMangoldt` | in Mathlib |  |
| 7-5 | 65 | Tchebychev 1852 bounds: 0.92 x/log x < pi(x) < 1.105 x/log x for large x | `Chebyshev.pi_ge`, `Chebyshev.psi_upper_clean`, `Chebyshev.a_bound` | partly in other libraries; not proved here |  |
| 7-6 | 65 | Identity: sum over d dividing n of Lambda(d) equals log n | `ArithmeticFunction.vonMangoldt_sum` | in Mathlib |  |
| 7-7 | 65 | Logarithmic derivative of Euler product: -zeta'(s)/zeta(s) = sum Lambda(n) n^(-s) for Re s > 1 | `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div` | in Mathlib |  |
| 7-8 | 66 | T(x) = sum_{m<=x} Lambda(m)[x/m] = log([x]!) | `Mertens.sum_log_eq_log_factorial` | in PrimeNumberTheoremAnd only (not a dependency) |  |
| 7-9 | 66 | Stirling: log([x]!) = x log x - x + O(log x) | `Chebyshev.T.ge` | in PrimeNumberTheoremAnd only (not a dependency) |  |
| 7-10 | 66 | T(x) - 2T(x/2) ~ x log 2 and lies below psi(x), giving pi(x) >> x/log x and pi(x)-pi(sqrt x) bounds, hence pi(x) << x/log x | `Chebyshev.psi_ge`, `Chebyshev.psi_le_const_mul_self`, `Chebyshev.pi_ge` | partly in other libraries; not proved here |  |
| 7-11 | 66 | Tchebychev's sharper combination T(x)-T(x/2)-T(x/3)-T(x/5)+T(x/30) giving constants in 7-5 | `Chebyshev.psi_lower`, `Chebyshev.a_bound` | in PrimeNumberTheoremAnd only (not a dependency) |  |
| 7-12 | 66 | Mertens 1874: sum_{p<=x} 1/p = log log x + A + O(1/log x) | `Mertens.E₂p.bound` | in PrimeNumberTheoremAnd only (not a dependency) |  |
| 7-13 | 67 | Mertens: sum_{p<=x} (log p)/p = log x + O(1) | `Mertens.E₁p.bounded` | in PrimeNumberTheoremAnd only (not a dependency) |  |
| 7-14 | 67 | Mertens: for nonprincipal chi, sum_p chi(p)/p converges | `DirichletCharacter.exists_tendsto_sum_Icc_eulerLogCoeff_div` | partly in other libraries; not proved here |  |
| 7-15 | 67 | Convergence of sum chi(n)(log n)/n for nonprincipal chi, and of sum chi(m)Lambda(m)/m (the proof device for 7-14) | `DirichletCharacter.tendsto_sum_Icc_div_LFunction_one` | partly in other libraries; not proved here |  |
| 7-16 | 67 | sum_{p<=x, p=a mod q} 1/p = (1/phi(q)) log log x + A(q,a) + O(1/log x) | — | partly in other libraries; not proved here |  |
| 7-17 | 68 | The Euler product for L(s,chi) holds also at s = 1 (conditionally convergent) for nonprincipal chi | `DirichletCharacter.tendsto_prod_primesLE_inv_LFunction_one` | in Tau Ceti only (not a dependency) |  |

## Chapter 8: Riemann's Memoir (book pp. 59-64; pdf pp. 69-74)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 8-1 | 69 | Riemann (a): zeta continues meromorphically to the plane with only a simple pole at s=1 of residue 1 | `differentiableAt_riemannZeta`, `riemannZeta_residue_one` | in Mathlib |  |
| 8-2 | 69 | Riemann (b): functional equation pi^(-s/2) Gamma(s/2) zeta(s) is invariant under s -> 1-s | `completedRiemannZeta_one_sub`, `completedRiemannZeta₀_one_sub`, `riemannZeta_one_sub` | in Mathlib |  |
| 8-3 | 69 | Trivial zeros: for Re s < 0 the only zeros of zeta are s = -2,-4,-6,... | `riemannZeta_eq_zero_iff_of_re_nonpos`, `riemannZeta_neg_two_mul_nat_add_one` | in Mathlib |  |
| 8-5 | 69 | Riemann (a'): zeta has infinitely many zeros in the critical strip, symmetric about the real axis and the line Re s = 1/2 | `riemannZeta_conj`, `riemannZeta_one_sub` | partly in other libraries; not proved here |  |
| 8-6 | 69 | Riemann (b'), von Mangoldt: N(T) = (T/2pi) log(T/2pi) - T/2pi + O(log T) | `NTKB.Davenport.zetaZeroCount_sub_le`, `NTKB.Davenport.integral_re_logDeriv_riemannXi_two`, `NTKB.abs_re_digamma_sub_log_le` | proved in part |  |
| 8-7 | 70 | Riemann (c'), Hadamard: xi(s) = s(s-1)pi^(-s/2)Gamma(s/2)zeta(s)/2 is entire and has product e^(A+Bs) prod (1-s/rho) e^(s/rho) | `riemannXi_entireOfOrderAtMost_one`, `riemannXi_hadamard_factorization_no_monomial` | in PrimeNumberTheoremAnd only (not a dependency) |  |
| 8-8 | 70 | Riemann (d'), von Mangoldt: psi(x) - x = -sum_rho x^rho/rho - zeta'(0)/zeta(0) - (1/2) log(1 - x^(-2)) | — | not formalized |  |
| 8-9 | 70 | Riemann Hypothesis: all nontrivial zeros have real part 1/2 | `RiemannHypothesis` | in Mathlib |  |
| 8-10 | 71 | Euler integral for Gamma and substitution t = pi n^2 x giving pi^(-s/2)Gamma(s/2) n^(-s) = integral of x^(s/2-1) e^(-pi n^2 x) dx | `Complex.integral_cpow_mul_exp_neg_mul_Ioi`, `Complex.Gamma_eq_integral`, `completedZeta_eq_tsum_of_one_lt_re` | in Mathlib |  |
| 8-11 | 71 | omega(x) = sum_{n>=1} e^(-pi n^2 x), and pi^(-s/2)Gamma(s/2)zeta(s) = integral of x^(s/2-1) omega(x) dx for Re s > 1 | — | in Mathlib |  |
| 8-12 | 72 | Theta functional equation theta(1/x) = x^(1/2) theta(x) for theta(x) = sum e^(-pi n^2 x), x > 0 | `jacobiTheta_S_smul` | in Mathlib |  |
| 8-13 | 72 | Riemann's integral formula pi^(-s/2)Gamma(s/2)zeta(s) = 1/(s(s-1)) + integral over [1,inf) of (x^(s/2-1) + x^(-s/2-1/2)) omega(x) dx, valid for all s | `differentiable_completedZeta₀`, `completedRiemannZeta_eq` | partly in other libraries; not proved here |  |
| 8-14 | 72 | zeta(0) = -1/2 (from the pole of Gamma(s/2) at 0) | `riemannZeta_zero` | in Mathlib |  |
| 8-15 | 73 | zeta(s) < 0 for 0 < s < 1 (via the integral bound, or alternatively via Ch 4 G) | — | not formalized |  |
| 8-16 | 73 | The even entire function xi(s) = (1/2) s(s-1)pi^(-s/2)Gamma(s/2)zeta(s) is entire and satisfies xi(s) = xi(1-s) | `Complex.differentiable_riemannXi`, `Complex.riemannXi_one_sub` | in PrimeNumberTheoremAnd only (not a dependency) |  |
| 8-17 | 73 | General theta functional equation: sum_n e^(-pi (n+a)^2 x) = x^(-1/2) sum_n e^(-pi n^2/x + 2 pi i n a) for real a, x > 0 | `jacobiTheta₂_functional_equation` | in Mathlib |  |

## Chapter 9: The Functional Equation of the L Functions (book pp. 65-72; pdf pp. 75-82)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 9-1 | 75 | Definition of the Gauss sum tau(chi) = sum_{m mod q} chi(m) e(m/q) of a character | — | in Mathlib |  |
| 9-2 | 75 | For (n,q)=1: chi(n) tau(chi) = sum_h chi(h) e(nh/q) | `gaussSum_mulShift`, `gaussSum_mulShift_eq` | in Mathlib |  |
| 9-3 | 76 | For primitive chi the identity 9-2 holds also when (n,q)>1 (both sides vanish), so chi(n) tau(chi-bar) is a Gauss-type sum for all n | `gaussSum_mulShift_of_isPrimitive` | in Mathlib |  |
| 9-4 | 76 | For primitive chi mod q,∣tau(chi)∣= sqrt q | `DirichletCharacter.norm_gaussSum_stdAddChar` | in Mathlib |  |
| 9-5 | 77 | Gauss sum of an imprimitive chi mod q = q1 r induced by chi1 vanishes unless (q1,r)=1, and then tau(chi) = mu(r) chi1(r) tau(chi1) | — | not formalized |  |
| 9-6 | 78 | Fourier expansion for primitive chi: chi(n) = (1/tau(chi-bar)) sum_m chi-bar(m) e(mn/q) | `DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`, `gaussSum_mulShift_of_isPrimitive` | partly in other libraries; not proved here |  |
| 9-7 | 78 | Theta-type functional equation psi(1/x,chi-bar)-relation: tau(chi) psi(1/x,chi-bar) = q^(1/2)... x^(1/2) psi(x,chi) for psi(x,chi)=sum chi(n) e^(-pi n^2 x/q), chi even | `ZMod.LFunction_one_sub`, `ZMod.completedLFunction_one_sub_even` | partly in other libraries; not proved here |  |
| 9-8 | 79 | Analytic continuation: L(s,chi) for nonprincipal chi is entire (even chi case) | `DirichletCharacter.differentiable_LFunction`, `DirichletCharacter.LFunction_eq_LSeries` | in Mathlib |  |
| 9-9 | 79 | Functional equation for primitive even chi: pi^(-s/2) q^(s/2) Gamma(s/2) L(s,chi) = (tau(chi)/q^(1/2)) pi^(-(1-s)/2)... Gamma((1-s)/2) L(1-s,chi-bar) | `DirichletCharacter.IsPrimitive.completedLFunction_one_sub` | in Mathlib |  |
| 9-10 | 79 | Zeros of L(s,chi) for Re s < 0 with chi even primitive: only at s = -2,-4,..., and also a zero at s = 0 | `DirichletCharacter.Even.LFunction_neg_two_mul_nat_add_one`, `DirichletCharacter.LFunction_eq_zero_iff_of_re_nonpos` | in Mathlib |  |
| 9-11 | 80 | Odd chi: psi_1(x,chi) = sum n chi(n) e^(-pi n^2 x/q) satisfies tau(chi) psi_1(x,chi) = i q^(1/2) x^(-3/2) psi_1(1/x,chi-bar)-type equation | `ZMod.completedLFunction_one_sub_odd` | partly in other libraries; not proved here |  |
| 9-12 | 80 | Differentiating the theta transformation in a: sum (n+a) e^(-pi (n+a)^2 x) = x^(-3/2) sum v e^(-pi v^2/x + 2 pi i v a) times -i-type constant | `jacobiTheta₂'_functional_equation`, `jacobiTheta₂_functional_equation` | in Mathlib |  |
| 9-13 | 81 | Functional equation for odd primitive chi: pi^(-(1-s)/2)... Gamma((2-s)/2) L(1-s,chi) = (tau(chi)/(i q^(1/2))) ... Gamma((s+1)/2) L(s,chi-bar) | `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`, `DirichletCharacter.Odd.LFunction_neg_two_mul_nat_sub_one` | in Mathlib |  |
| 9-14 | 81 | Unified form: with a = 0 or 1 by parity, xi-type function Lambda(s,chi) = (pi/q)^(-(s+a)/2) Gamma((s+a)/2) L(s,chi) satisfies Lambda(1-s,chi-bar) = (i^a q^(1/2)/tau(chi)) Lambda(s,chi) | `DirichletCharacter.completedLFunction`, `DirichletCharacter.gammaFactor`, `DirichletCharacter.IsPrimitive.completedLFunction_one_sub` | in Mathlib |  |
| 9-15 | 81 | Definition of the Hurwitz zeta function zeta(s,a) = sum_{n>=0} (n+a)^(-s), 0<a<=1; zeta(s,1) = zeta(s), zeta(s,1/2) = (2^s-1) zeta(s) | `HurwitzZeta.hurwitzZeta`, `HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re`, `HurwitzZeta.hurwitzZeta_zero` | partly in other libraries; not proved here |  |
| 9-16 | 81 | zeta(s,a) continues meromorphically with a simple pole at s=1 (residue 1) | `HurwitzZeta.differentiableAt_hurwitzZeta`, `HurwitzZeta.hurwitzZeta_residue_one` | in Mathlib |  |
| 9-17 | 81 | L(s,chi) = q^(-s) sum_{m=1}^q chi(m) zeta(s,m/q) | `ZMod.LFunction`, `ZMod.LFunction_eq_LSeries` | in Mathlib |  |
| 9-18 | 82 | Hurwitz formula: for Re s<0, zeta(s,a) = (2 Gamma(1-s)/(2 pi)^(1-s)) (sum cos(2 pi m a ...)/m^(1-s) + sum sin(...)/m^(1-s)) | `HurwitzZeta.hurwitzZeta_one_sub` | in Mathlib |  |
| 9-19 | 82 | Heilbronn-Davenport and Cassels: for a rational (not 1 or 1/2), transcendental, or algebraic irrational, zeta(s,a) has zeros with Re s>1 | — | not formalized |  |

## Chapter 10: Properties of the Gamma Function (book p. 73; pdf p. 83)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 10-1 | 83 | Euler's integral: Gamma(s) = integral over (0,inf) of e^(-t) t^(s-1) dt for Re s > 0 | `Complex.Gamma_eq_integral`, `Complex.GammaIntegral` | in Mathlib |  |
| 10-2 | 83 | Weierstrass product 1/Gamma(s) = s e^(gamma s) prod (1+s/n) e^(-s/n); Gamma has no zeros and simple poles at 0,-1,-2,... | `Complex.Gamma_ne_zero`, `Complex.GammaSeq_tendsto_Gamma` | partly in other libraries; not proved here |  |
| 10-3 | 83 | Recurrence Gamma(s+1) = s Gamma(s) | `Complex.Gamma_add_one` | in Mathlib |  |
| 10-4 | 83 | Reflection: Gamma(s) Gamma(1-s) = pi / sin(pi s) | `Complex.Gamma_mul_Gamma_one_sub` | in Mathlib |  |
| 10-5 | 83 | Legendre duplication: Gamma(s) Gamma(s+1/2) = 2^(1-2s) sqrt(pi) Gamma(2s) | `Complex.Gamma_mul_Gamma_add_half` | in Mathlib |  |
| 10-6 | 83 | Combined: pi^(-1/2) Gamma(s/2) / Gamma((1-s)/2) = 2^(-s)... cos(pi s/2) Gamma(s) (converts the symmetric functional equation of zeta to the unsymmetric one) | — | not formalized |  |
| 10-7 | 83 | Unsymmetric functional equation: zeta(1-s) = 2^(1-s) pi^(-s) cos(pi s/2) Gamma(s) zeta(s) | `riemannZeta_one_sub` | in Mathlib |  |
| 10-8 | 83 | Stirling: log Gamma(s) = (s-1/2) log s - s + (1/2) log 2 pi + O(1/∣s∣) as∣s∣-> infinity in∣arg s∣<= pi - delta | — | partly in other libraries; not proved here |  |
| 10-9 | 83 | Digamma asymptotic: Gamma'(s)/Gamma(s) = log s + O(1/∣s∣) in the same angle | — | partly in other libraries; not proved here |  |

## Chapter 11: Integral Functions of Order 1 (book pp. 74-78; pdf pp. 84-88)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 11-3 | 84 | An entire function of finite order without zeros is e^(g(z)) with g a polynomial, of degree equal to the order | `NTKB.Davenport.zeroFree_finiteOrder_eq_exp_polynomial`, `NTKB.exists_polynomial_of_norm_le_on_circles` | proved |  |
| 11-4 | 85 | Jensen's formula: (1/2pi) integral of log∣f(Re^(i theta))∣dtheta - log∣f(0)∣= log(R^n/(∣z_1∣...∣z_n∣)) for f with zeros z_1..z_n in∣z∣<R | `MeromorphicOn.circleAverage_log_norm`, `AnalyticOnNhd.circleAverage_log_norm`, `NTKB.card_le_of_jensen` | in Mathlib |  |
| 11-5 | 85 | Same right-hand side as the integral of n(r)/r dr over (0,R), where n(r) counts zeros in∣z∣<r | `NTKB.Davenport.integral_zeroCount_div` | proved | Mathlib: `AnalyticOnNhd.circleAverage_log_norm`, Mathlib: `Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const` |
| 11-6 | 85 | Consequence of Jensen: if f has order <= rho then n(R) = O(R^a) for any a > rho | `NTKB.Davenport.zeroCount_isBigO`, `NTKB.exists_card_le_rpow` | proved |  |
| 11-7 | 86 | For order 1: the series sum over zeros of∣z_n∣^(-1-eps) converges for every eps > 0 | `NTKB.Davenport.summable_norm_zero_rpow_neg` | proved |  |
| 11-8 | 86 | Canonical product P(z) = prod (1 - z/z_n) e^(z/z_n) converges absolutely, locally uniformly, to an entire function with exactly the zeros z_n | `NTKB.canonicalProductOne`, `NTKB.hasProdLocallyUniformlyOn_canonicalProductOne`, `NTKB.differentiable_canonicalProductOne`, `NTKB.canonicalProductOne_ne_zero`, `NTKB.analyticOrderAt_canonicalProductOne` | proved | `Complex.differentiable_canonicalProduct`, `Complex.canonicalProduct_eq_zero_iff` |
| 11-9 | 86 | Lower bound∣P(z)∣>= exp(-R^(1+eps)) on circles∣z∣= R chosen away from the∣z_n∣(via sub-products P1,P2,P3) | `NTKB.norm_canonicalProductOne_ge`, `NTKB.exists_good_radius` | proved |  |
| 11-10 | 87 | Hadamard for order 1: f(z) = e^(A+Bz) prod (1 - z/z_n) e^(z/z_n) for an entire function of order at most 1 (the quotient F = f/P is e^(g) with deg g <= 1) | `NTKB.Davenport.hadamard_factorization_order_one` | proved |  |
| 11-11 | 88 | If sum 1/∣z_n∣converges then the order-1 function satisfies∣f(z)∣< e^(C∣z∣) (from∣(1-w)e^w∣<= e^(∣w∣^2)... style inequality) | `NTKB.Davenport.norm_le_exp_of_summable_inv` | proved |  |
| 11-12 | 88 | Summary: an entire function of order 1 has the form in 11-10, sum r_n^(-1-eps) converges, and if sum r_n^(-1) converges then f is of exponential type | `NTKB.Davenport.entire_order_one_summary` | proved | `Complex.Hadamard.summable_norm_inv_rpow_divisorZeroIndex₀_of_growth` |

## Chapter 12: The Infinite Products for xi(s) and xi(s,chi) (book pp. 79-83; pdf pp. 89-93)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 12-1 | 89 | Definition xi(s) = (1/2) s(s-1) pi^(-s/2) Gamma(s/2) zeta(s), an entire function with xi(s) = xi(1-s) | `NTKB.riemannXi`, `NTKB.riemannXi_eq`, `NTKB.differentiable_riemannXi`, `NTKB.riemannXi_one_sub`, `NTKB.riemannXi_eq_zero_iff` | proved | `Complex.differentiable_riemannXi`, `Complex.riemannXi_one_sub` |
| 12-2 | 89 | Growth bound∣xi(s)∣< exp(C∣s∣log∣s∣), hence xi has order at most 1 | `NTKB.Davenport.norm_riemannXi_le_exp`, `NTKB.Davenport.entireOrder_riemannXi_le_one` | proved | `completedRiemannZeta₀_entireOfOrderAtMost_one`, `Complex.completedRiemannZeta₀_order_one` |
| 12-3 | 89 | Crude bound zeta(s) = O(∣s∣) for Re s >= 1/2 from the integral representation of Ch 4 | `NTKB.Davenport.norm_riemannZeta_le_mul_norm` | proved | `norm_riemannZeta_lt_linear_im_on_strip` |
| 12-4 | 89 | The bound in 12-2 is essentially sharp on the real axis, so xi has exact order 1 and fails the exponential-type bound | `NTKB.Davenport.riemannXi_not_exponential_type`, `NTKB.Davenport.entireOrder_riemannXi` | proved |  |
| 12-5 | 90 | xi has infinitely many zeros rho; sum∣rho∣^(-1-eps) converges for every eps > 0 but sum∣rho∣^(-1) diverges | `NTKB.Davenport.riemannXi_zeros` | proved | `Complex.Hadamard.summable_norm_inv_rpow_divisorZeroIndex₀_of_growth` |
| 12-6 | 90 | Hadamard product xi(s) = e^(A+Bs) prod_rho (1 - s/rho) e^(s/rho) | `NTKB.Davenport.riemannXi_hadamard` | proved | `riemannXi_hadamard_factorization` |
| 12-7 | 90 | Partial fractions: zeta'(s)/zeta(s) = B - 1/(s-1) + sum_rho (1/(s-rho) + 1/rho) + (1/2) log pi - (1/2) Gamma'(s/2+1)/Gamma(s/2+1) | `NTKB.Davenport.logDeriv_riemannXi`, `NTKB.Davenport.logDeriv_riemannZeta`, `NTKB.logDeriv_canonicalProductOne`, `NTKB.logDeriv_exp_mul_canonicalProductOne` | proved | `Kadiri.neg_zeta_logDeriv_eq_of_genusOne_hadamard` |
| 12-8 | 90 | Digamma identity: Gamma'(s/2+1)/(2 Gamma(s/2+1)) = -gamma/2 + sum_{n>=1} (1/(2n) - 1/(2n+s)) | `NTKB.Davenport.digamma_half_add_one`, `NTKB.Davenport.digamma_eq_tsum`, `NTKB.Davenport.Gamma_inv_eq_product`, `NTKB.norm_digamma_add_inv_le` | proved | `Complex.digamma_eq_tsum` |
| 12-9 | 91 | Constant A: e^A = xi(0) = 1/2 | `NTKB.Davenport.riemannXi_hadamard_constants` | proved | `analyticOrderNatAt_riemannXi_zero` |
| 12-10 | 91 | B = -gamma/2 - 1 + (1/2) log 4 pi | `NTKB.Davenport.riemannXi_hadamard_constants` | proved |  |
| 12-11 | 92 | B = -sum_rho Re(1/rho) = -2 sum_{gamma>0} Re 1/rho, summed with rho and its conjugate grouped; B is about -0.023, so every zero has∣Im rho∣> 6 | `NTKB.Davenport.riemannXi_B_eq_neg_tsum` | proved |  |
| 12-12 | 92 | Definition for primitive chi mod q: xi(s,chi) = (q/pi)^((s+a)/2) Gamma((s+a)/2) L(s,chi), with a = 0 or 1 by parity; entire | `NTKB.dirichletXi`, `NTKB.dirichletXi_eq`, `NTKB.differentiable_dirichletXi` | proved | Mathlib: `DirichletCharacter.completedLFunction`, Mathlib: `DirichletCharacter.differentiable_completedLFunction` |
| 12-13 | 92 | Functional equation xi(1-s,chi-bar) = (i^a q^(1/2)/tau(chi)) xi(s,chi), multiplier of modulus 1 | `NTKB.dirichletXi_one_sub` | proved | Mathlib: `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`, Mathlib: `DirichletCharacter.norm_rootNumber` |
| 12-14 | 92 | Bound∣L(s,chi)∣<= 2q∣s∣for Re s >= 1/2 (partial summation) and hence∣xi(s,chi)∣< q^(1/2+a) exp(C∣s∣log∣s∣) | `NTKB.Davenport.norm_LFunction_le_mul`, `NTKB.Davenport.norm_dirichletXi_le_exp` | proved | Tau Ceti: `DirichletCharacter.norm_LFunction_le_level_mul_norm_div_re` |
| 12-15 | 92 | xi(s,chi) has order 1, infinitely many zeros rho in the critical strip with sum∣rho∣^(-1-eps) convergent and sum∣rho∣^(-1) divergent | `NTKB.Davenport.entireOrder_dirichletXi_le_one`, `NTKB.dirichletXi_eq_zero_iff`, `NTKB.Davenport.dirichletXi_zeros`, `NTKB.Davenport.dirichletXi_zeros_infinite`, `NTKB.Davenport.dirichletXi_not_exponential_type` | proved |  |
| 12-16 | 92 | Hadamard product xi(s,chi) = e^(A(chi)+B(chi)s) prod (1 - s/rho) e^(s/rho), with e^(A(chi)) = xi(0,chi) related to L(1,chi-bar) | `NTKB.Davenport.dirichletXi_hadamard`, `NTKB.Davenport.dirichletXi_hadamard_exp_A` | proved |  |
| 12-17 | 93 | Partial fractions: L'/L(s,chi) = B(chi) - (1/2) log(q/pi) ... + sum_rho (1/(s-rho) + 1/rho) - (1/2) Gamma'/Gamma((s+a)/2) | `NTKB.Davenport.logDeriv_LFunction` | proved |  |
| 12-18 | 93 | Re B(chi) = -sum_rho Re(1/rho) over zeros of L(s,chi) (using symmetry rho -> 1-rho-bar); B(chi) real and negative for real chi | `NTKB.Davenport.re_B_eq_neg_tsum`, `NTKB.Davenport.B_real_neg_of_real` | proved |  |
| 12-19 | 93 | Zeros of L(s,chi) are symmetric about Re s = 1/2 (1 - rho = conjugate of a zero of chi-bar... ) but for complex chi not about the real axis | `NTKB.Davenport.dirichletXi_zero_symm`, `NTKB.dirichletXi_inv_conj` | proved |  |

## Chapter 13: A Zero-Free Region for zeta(s) (book pp. 84-87; pdf pp. 94-97)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 13-1 | 94 | Hadamard and de la Vallee Poussin 1896: zeta(s) <> 0 on Re s = 1 | `riemannZeta_ne_zero_of_one_le_re`, `DirichletCharacter.LFunction_ne_zero_of_re_eq_one` | in Mathlib |  |
| 13-2 | 94 | For Re s > 1: log zeta(s) = sum_p sum_m m^(-1) p^(-ms), so Re log zeta(sigma+it) = sum sum m^(-1) p^(-m sigma) cos(t m log p) | `riemannZeta_eulerProduct_exp_log`, `DirichletCharacter.LSeries_eulerProduct_exp_log`, `DirichletCharacter.summable_neg_log_one_sub_mul_prime_cpow` | partly in other libraries; not proved here |  |
| 13-3 | 94 | Mertens' trigonometric inequality 3 + 4 cos theta + cos 2 theta >= 0 (it equals 2(1+cos theta)^2) | `NTKB.Davenport.three_add_four_cos_add_cos_two_mul` | proved | Tau Ceti: `TauCeti.LSeries.threeFourOneCombination_eq_two_mul_sq`, Tau Ceti: `TauCeti.LSeries.threeFourOneCombination_nonneg` |
| 13-4 | 95 | Consequence: zeta(sigma)^3∣zeta(sigma+it)∣^4∣zeta(sigma+2it)∣>= 1 for sigma > 1 | `DirichletCharacter.norm_LFunction_product_ge_one`, `DirichletCharacter.norm_LSeries_product_ge_one` | in Mathlib |  |
| 13-5 | 95 | A zero of zeta at 1+it contradicts 13-4 as sigma -> 1+, because zeta has only a simple pole at 1 | `DirichletCharacter.LFunction_ne_zero_of_re_eq_one` | in Mathlib |  |
| 13-6 | 95 | Logarithmic derivative: -zeta'(s)/zeta(s) = sum Lambda(n) n^(-sigma) cos(t log n) real part, for Re s > 1 | `NTKB.Davenport.three_four_one_riemannZeta` | proved | Mathlib: `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div` |
| 13-7 | 95 | Basic inequality C): 3(-zeta'/zeta(sigma)) + 4 Re(-zeta'/zeta(sigma+it)) + Re(-zeta'/zeta(sigma+2it)) >= 0 | `NTKB.Davenport.three_four_one_riemannZeta` | proved |  |
| 13-8 | 95 | Behaviour at the pole: -zeta'(sigma)/zeta(sigma) < 1/(sigma-1) + A for 1 < sigma < 2 | `NTKB.Davenport.neg_logDeriv_riemannZeta_real_le` | proved |  |
| 13-9 | 95 | Partial fraction bound: -Re zeta'/zeta(s) < A log t - Re sum_rho 1/(s-rho) for 1 < sigma < 2, t > 2 | `NTKB.Davenport.neg_re_logDeriv_riemannZeta_eq`, `NTKB.Davenport.neg_re_logDeriv_riemannZeta_le` | proved |  |
| 13-10 | 96 | Applying 13-9 at s = sigma+2it with the zero sum dropped, and at s = sigma+it keeping the single term of a zero beta+i gamma: -Re zeta'/zeta(sigma+2it) < A log t, and -Re zeta'/zeta(sigma+i gamma) < A log t - 1/(sigma-beta) | `NTKB.Davenport.neg_re_logDeriv_riemannZeta_le_log`, `NTKB.Davenport.neg_re_logDeriv_riemannZeta_le_zero` | proved | `ShiftOneBound` |
| 13-11 | 96 | Theorem (de la Vallee Poussin 1899): there is c > 0 with zeta(s) <> 0 for sigma > 1 - c/log t, t > 2 | `NTKB.Davenport.riemannZeta_zero_free_region` | proved | `ZetaZeroFree1` |
| 13-12 | 96 | Combined form: zeta has no zero in sigma >= 1 - c/log(∣t∣+2) for all t | `NTKB.Davenport.riemannZeta_zero_free_region_all` | proved | `ZetaZeroFree1` |
| 13-13 | 97 | Littlewood 1922: zero-free region of breadth c log log t / log t | — | not formalized |  |
| 13-14 | 97 | Vinogradov-Korobov 1958: zero-free region of breadth c(a)/(log t)^a for a > 2/3 | — | not formalized |  |

## Chapter 14: Zero-Free Regions for L(s,chi) (book pp. 88-96; pdf pp. 98-106)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 14-1 | 98 | Logarithmic derivative of the Euler product: -L'/L(s,chi) = sum Lambda(n) chi(n) n^(-s) for Re s > 1 | `DirichletCharacter.LSeries_twist_vonMangoldt_eq` | in Mathlib |  |
| 14-2 | 98 | Basic inequality A): 3(-L'/L)(sigma,chi_0) + 4 Re(-L'/L)(sigma+it,chi) + Re(-L'/L)(sigma+2it,chi^2) >= 0 for sigma > 1 | `NTKB.Davenport.three_four_one_LFunction` | proved | Mathlib: `DirichletCharacter.norm_LFunction_product_ge_one` |
| 14-4 | 99 | Behaviour at the pole for the principal character: -L'/L(sigma,chi_0) < 1/(sigma-1) + c1 for 1 < sigma < 2 | `NTKB.neg_logDeriv_one_real_le` | proved | Mathlib: `DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta`, Mathlib: `DirichletCharacter.LFunctionTrivChar_residue_one` |
| 14-5 | 99 | For primitive chi and Re s > 1: -Re L'/L(s,chi) < c2 𝔏 - Re sum_rho 1/(s-rho) | `NTKB.Davenport.neg_re_logDeriv_LFunction_eq`, `NTKB.Davenport.neg_re_logDeriv_LFunction_le` | proved |  |
| 14-6 | 99 | Relation of an imprimitive chi to the primitive chi1 inducing it: L(s,chi) = L(s,chi1) prod_{p∣q} (1 - chi1(p) p^(-s)), so L'/L differs from L1'/L1 by O(log q) | `NTKB.Davenport.norm_logDeriv_LFunction_changeLevel_sub_le` | proved |  |
| 14-7 | 100 | Complex characters: there is c5 > 0 such that every zero beta + i gamma of L(s,chi), chi complex mod q, has beta < 1 - c5/𝔏 | `NTKB.Davenport.LFunction_zero_free_complex_primitive` | proved |  |
| 14-8 | 100 | Same zero-free region holds for imprimitive complex chi, since the extra zeros lie on Re s = 0 | `NTKB.Davenport.LFunction_zero_free_complex` | proved | Tau Ceti: `DirichletCharacter.LFunction_changeLevel_eq_zero_iff` |
| 14-9 | 101 | Real nonprincipal chi: for 0 < delta < c8 any zero beta+i gamma with∣gamma∣>= delta/log q satisfies beta < 1 - c9 delta/𝔏 | `NTKB.Davenport.LFunction_zero_free_real_primitive`, `NTKB.Davenport.LFunction_zero_free_real`, `NTKB.Davenport.LFunction_zero_free_real'` | proved in part |  |
| 14-10 | 101 | Real nonprincipal chi: in∣gamma∣< delta/log q there is at most one zero with beta > 1 - delta'/log q and it is real and simple | `NTKB.Davenport.LFunction_exceptional_zero_unique`, `NTKB.Davenport.LFunction_exceptional_zero_real_simple` | proved |  |
| 14-11 | 103 | Theorem: there is an absolute constant c14 so that for complex chi mod q, L(s,chi) has no zero in sigma > 1 - c14/log(q(∣t∣+2)) (for∣t∣< 1: 1 - c14/log q); for real chi mod q the only possible zero in that region is one simple real zero | `NTKB.Davenport.LFunction_zero_free_theorem_complex`, `NTKB.Davenport.LFunction_zero_free_theorem_real`, `NTKB.Davenport.LFunction_zero_free_theorem_real_simple` | proved |  |
| 14-12 | 103 | Landau: for distinct real primitive chi1, chi2 mod q1, q2 with real zeros beta1, beta2, min(beta1,beta2) < 1 - c15/log(q1 q2) | `NTKB.Davenport.landau_real_zeros`, `NTKB.Davenport.landau_positivity`, `NTKB.Davenport.landau_hne_of_ne_level`, `NTKB.Davenport.landau_hne_of_ne` | proved |  |
| 14-13 | 104 | At most one real nonprincipal chi mod q has L(s,chi) with a zero in the region of 14-11 | `NTKB.Davenport.at_most_one_exceptional_character`, `NTKB.Davenport.psiAP_sub_le` | proved in part |  |
| 14-14 | 104 | If chi_j (mod q_j) are real primitive with real zeros beta_j > 1 - c19/log q_j, then the q_j grow at least geometrically: log q_{j+1}/log q_j bounded below, so such q_j are very rare | `NTKB.Davenport.exceptional_moduli_grow` | proved |  |
| 14-15 | 105 | Page: for z >= 3 there is at most one real primitive chi to a modulus q <= z with a real zero beta > 1 - c20/log z | `NTKB.Davenport.page_exceptional_character` | proved |  |
| 14-16 | 105 | Lower bound L(1,chi) > c21 q^(-1/2) for real primitive chi, from h(d) >= 1 and the class number formula | `TauCeti.NumberField.classNumber_eq_LFunction_one_of_discr_ne` | partly in other libraries; not proved here |  |
| 14-17 | 105 | Derivative bound:∣L'(sigma,chi)∣< c22 log^2 q for 1 - 1/log q <= sigma < 1 | `NTKB.Davenport.norm_deriv_LFunction_near_one_le`, `NTKB.norm_LFunction_le_euler` | proved in part |  |
| 14-18 | 106 | Effective bound for a real zero: beta < 1 - c23/(q^(1/2) log^2 q) for real nonprincipal chi; improved by a factor log q for even chi | — | not formalized |  |
| 14-19 | 106 | Bound∣L(sigma,chi)∣< c25 log q for 1 - 1/log q < sigma < 1 | `NTKB.Davenport.norm_LFunction_near_one_le` | proved | Tau Ceti: `DirichletCharacter.norm_LFunction_one_le_two_add_log` |

## Chapter 15: The number N(T) (book pp. 97-100; pdf pp. 107-110)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 15-1 | 107 | 2 pi N(T) equals the change of arg xi(s) around the rectangle with vertices 2, 2+iT, -1+iT, -1 (argument principle for the zero count) | `NTKB.Davenport.rectIntegral_logDeriv_riemannXi`, `NTKB.zetaZeroCount` | proved in part |  |
| 15-2 | 107 | By the symmetry xi(s)=xi(1-s) the left half of the contour equals the right half, so pi N(T) is the change of arg xi along 2 -> 2+iT -> 1/2+iT | `NTKB.Davenport.rectIntegral_logDeriv_riemannXi_eq`, `NTKB.Davenport.pi_mul_zetaZeroCount_eq` | proved in part |  |
| 15-3 | 108 | N(T) = (T/2pi) log(T/2pi) - T/2pi + 7/8 + S(T) + O(1/T), the Riemann-von Mangoldt formula (displayed (1) of Sect. 8 follows from S(T)=O(log T)) | `NTKB.Davenport.zetaZeroCount_sub_le`, `NTKB.Davenport.integral_re_logDeriv_riemannXi_two`, `NTKB.abs_re_digamma_sub_log_le` | proved in part |  |
| 15-5 | 108 | S(T) = O(log T) | `NTKB.Davenport.abs_integral_im_logDeriv_riemannXi_le` | proved in part |  |
| 15-6 | 108 | Lemma (C): sum over nontrivial zeros rho=beta+i gamma of 1/(1+(T-gamma)^2) is O(log T) | `NTKB.Davenport.sum_zeta_zeros_inv_one_add_sq_le` | proved |  |
| 15-7 | 109 | Corollary (a): the number of zeros with T-1<gamma<T+1 is O(log T) | `NTKB.Davenport.card_zeta_zeros_near_le` | proved |  |
| 15-8 | 109 | Corollary (b): sum of (T-gamma)^(-2) over zeros with abs(T-gamma)>1 is O(log T) | `NTKB.Davenport.sum_zeta_zeros_far_le` | proved |  |
| 15-9 | 109 | For t large not an ordinate and -1<sigma<2: zeta'/zeta(s) = sum over zeros with abs(t-gamma)<1 of 1/(s-rho) + O(log t) | `NTKB.Davenport.logDeriv_riemannZeta_local` | proved |  |
| 15-10 | 110 | The ordinates satisfy gamma_n ~ 2 pi n / log n | `NTKB.Davenport.tendsto_zetaZeroCount_div` | proved in part |  |
| 15-11 | 110 | Littlewood 1924: gamma_{n+1}-gamma_n tends to 0 | — | not formalized |  |
| 15-12 | 110 | N(T+H)-N(T) > A(H) log T for every fixed H>0 (Titchmarsh); so 15-7 is sharp | — | not formalized |  |
| 15-13 | 110 | Littlewood: the integral of S(t) from 0 to T is O(log T), showing cancellation in S | — | not formalized |  |

## Chapter 16: The number N(T, chi) (book pp. 100-103; pdf pp. 110-113)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 16-1 | 111 | Definition of N(T,chi) as the number of zeros of L(s,chi), chi primitive, in 0<sigma<1, abs(t)<T | `NTKB.LZeroCount` | proved |  |
| 16-2 | 111 | (1/2) N(T,chi) = (T/2pi) log(qT/2pi) - T/2pi + O(log T + log q) for T>=2, chi primitive mod q | `NTKB.Davenport.LZeroCount_sub_le`, `NTKB.Davenport.integral_re_logDeriv_dirichletXi`, `NTKB.abs_re_digamma_sub_log_le_half` | proved |  |
| 16-3 | 111 | 2 pi [N(T,chi)+1] = change of arg xi(s,chi) around the rectangle with vertices 3/2-iT, 3/2+iT, -1/2+iT, -1/2-iT (one trivial zero inside) | `NTKB.Davenport.rectIntegral_logDeriv_dirichletXi`, `NTKB.Davenport.pi_mul_LZeroCount_eq` | proved in part |  |
| 16-4 | 112 | arg L(1/2+iT,chi) = O(log T + log q), the analog of S(T)=O(log T) | `NTKB.Davenport.abs_integral_im_logDeriv_dirichletXi_le` | proved in part |  |
| 16-5 | 112 | Lemma: for real t, the sum over nontrivial zeros rho=beta+i gamma of 1/(1+(t-gamma)^2) is O(log(q(abs(t)+2))) | `NTKB.Davenport.sum_L_zeros_inv_one_add_sq_le` | proved |  |
| 16-6 | 112 | Corollary: the number of zeros with abs(t-gamma)<1 is O(log(q(abs(t)+2))) | `NTKB.Davenport.card_L_zeros_near_le` | proved |  |
| 16-7 | 112 | L'/L(s,chi) = sum over zeros with abs(t-gamma)<1 of 1/(s-rho) + O(log(q(abs(t)+2))) for -1<sigma<2 and t not an ordinate | `NTKB.Davenport.logDeriv_LFunction_local`, `NTKB.Davenport.norm_logDeriv_LFunction_left` | proved |  |
| 16-8 | 112 | For large q, at least a constant times log q zeros have abs(t) below an absolute constant, so the O(log q) bound in 16-5 at t=0 is best possible | `NTKB.Davenport.LZeroCount_ge_log` | proved |  |
| 16-9 | 112 | For imprimitive chi induced by chi_1 mod q_1, the formula 16-2 holds with q replaced by q_1 | — | not formalized |  |
| 16-10 | 113 | With the extra zeros of the Euler factors on sigma=0 included, N_0(T,chi) = (T/pi) log(q_1/(2 pi)... ) + O(T log q), spaced 2pi/log p apart | — | not formalized |  |

## Chapter 17: The explicit formula for psi(x) (book pp. 104-110; pdf pp. 114-120)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 17-2 | 114 | von Mangoldt: psi_0(x) = x - sum_rho x^rho/rho - zeta'(0)/zeta(0) - (1/2) log(1-x^(-2)) for x>1, symmetric summation over nontrivial zeros | `NTKB.Davenport.tendsto_explicitMain` | proved in part |  |
| 17-3 | 114 | zeta'(0)/zeta(0) = log 2 pi | `NTKB.Davenport.logDeriv_riemannZeta_zero` | proved | Mathlib: `riemannZeta_zero`, Mathlib: `deriv_riemannZeta_zero` |
| 17-4 | 114 | Sum over n of Lambda(n) n^(-s) = -zeta'(s)/zeta(s) for Re s>1 | `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`, `ArithmeticFunction.LSeriesSummable_vonMangoldt` | in Mathlib |  |
| 17-5 | 115 | Discontinuous integral: (1/2 pi i) int_{c-i inf}^{c+i inf} y^s/s ds equals 0 for 0<y<1, 1/2 at y=1, 1 for y>1 (c>0) | `NTKB.Davenport.perron_discontinuous_integral` | proved |  |
| 17-6 | 115 | Lemma (Perron truncation): the difference between I(y,T) and the step function delta(y) is O(y^c min(1, 1/(T times abs(log y)))) for y != 1 and O(c/T) at y=1 | `NTKB.Davenport.perron_truncated`, `NTKB.rectIntegral_inv_sub`, `NTKB.rectIntegral_eq_sum_residues` | proved in part |  |
| 17-7 | 116 | (C) abs(psi_0(x) - J(x,T)) is bounded by a sum over n of Lambda(n)(x/n)^c min(1, 1/(T abs(log x/n))) plus c Lambda(x)/T | `NTKB.Davenport.hasSum_explicitJ` | proved |  |
| 17-8 | 117 | (E) with c=1+1/log x: abs(psi_0(x) - J(x,T)) << x log^2 x / T + log x min(1, x/(T d(x))), where d(x) is the distance to the nearest prime power other than x | `NTKB.Davenport.norm_psi0_sub_explicitJ_le`, `NTKB.psi0` | proved in part |  |
| 17-9 | 118 | Choice of T: one can adjust T by O(1) so that abs(gamma - T) >> 1/log T for every zero | `NTKB.Davenport.exists_good_height` | proved |  |
| 17-10 | 118 | On the horizontal lines Im s = +-T with -1<sigma<2, zeta'/zeta = O(log^2 T) for the good T | `NTKB.Davenport.norm_logDeriv_riemannZeta_good_line` | proved |  |
| 17-11 | 118 | (8) zeta'/zeta(s) = O(log(2 abs(s))) for sigma<=-1 outside discs of radius 1/2 around -2,-4,... | `NTKB.Davenport.norm_logDeriv_LFunction_left_le`, `NTKB.logDeriv_dirichletXi_one_sub`, `NTKB.logDeriv_dirichletXi_eq`, `NTKB.Davenport.norm_logDeriv_riemannZeta_left_le` | proved in part |  |
| 17-12 | 119 | Unsymmetric functional equation zeta(1-s) = 2 (2 pi)^(-s) cos(pi s/2) Gamma(s) zeta(s) | `riemannZeta_one_sub` | in Mathlib |  |
| 17-13 | 119 | (9) finite explicit formula: psi_0(x) = x - sum over abs(gamma)<T of x^rho/rho - zeta'(0)/zeta(0) - (1/2) log(1-x^(-2)) + R(x,T), with (10) abs(R(x,T)) << x log^2(xT)/T + log x min(1, x/(T d(x))) for 2<=T | `NTKB.Davenport.norm_explicitJ_sub_main_le`, `NTKB.Davenport.explicit_formula_psi0` | proved in part |  |
| 17-14 | 120 | The restriction on T in 17-13 can be dropped (varying T by O(1) changes the sum by O(x log T / T)) | `NTKB.Davenport.explicit_formula_psi0` | proved in part |  |
| 17-15 | 120 | (11) For x an integer, abs(R(x,T)) << x (log xT)^2 / T | `NTKB.Davenport.explicit_formula_psi0` | proved in part |  |
| 17-16 | 120 | The formula also holds for 1<x<2 with a slightly different error term; for 0<x<1 see Ingham | — | not formalized |  |
| 17-17 | 119 | Explicit formula converges uniformly on closed x-intervals avoiding prime powers, not at prime powers | — | not formalized |  |

## Chapter 18: The prime number theorem (book pp. 111-114; pdf pp. 121-124)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 18-1 | 121 | psi(x) = x + O(x exp(-c sqrt(log x))) (de la Vallee Poussin error term) | `NTKB.Davenport.psi_sub_self_le` | proved |  |
| 18-2 | 121 | sum over zeros with 0<gamma<T of 1/gamma is O(log^2 T), via partial summation from N(t) << t log t | `NTKB.Davenport.sum_zeros_inv_norm_le` | proved |  |
| 18-3 | 121 | Choosing T with (log T)^2 = log x and combining 17-13 with the zero-free region gives psi(x)-x = O(x exp(-c sqrt(log x))) | `NTKB.Davenport.psi_sub_self_le` | proved |  |
| 18-4 | 122 | Passage to pi_1(x)=sum over n<=x of Lambda(n)/log n by partial summation: pi_1(x) = psi(x)/log x + int_2^x psi(t)/(t log^2 t) dt + O(1) | `NTKB.primeCountingOne`, `NTKB.Davenport.primeCountingOne_eq` | proved | Mathlib: `Chebyshev.primeCounting_eq_theta_div_log_add_integral` |
| 18-5 | 122 | pi_1(x) = li x + O(x exp(-c_3 sqrt(log x))) | `NTKB.Davenport.primeCounting_sub_logIntegral_le`, `NTKB.Davenport.primeCountingOne_sub_logIntegral_le` | proved in part |  |
| 18-6 | 123 | pi(x) differs from pi_1(x) by O(sqrt x), hence pi(x) = li x + O(x exp(-c_3 sqrt(log x))) (PNT with de la Vallee Poussin error) | `NTKB.Davenport.primeCounting_sub_logIntegral_le` | proved in part | `FKS2.corollary_22_tail` |
| 18-7 | 123 | Vinogradov-Korobov 1958: pi(x) = li x + O(x exp(-c (log x)^(3/5-eps))) from the improved zero-free region | — | not formalized |  |
| 18-8 | 123 | Under RH, psi(x) = x + O(x^(1/2) log^2 x) (von Koch), using sum 1/∣rho∣<< log^2 T and T = x^(1/2) | `NTKB.Davenport.psi_sub_self_le_of_riemannHypothesis` | proved |  |
| 18-9 | 123 | Under RH, pi(x) = li x + O(x^(1/2) log x) | `NTKB.Davenport.primeCounting_sub_logIntegral_le_of_riemannHypothesis` | proved |  |
| 18-10 | 123 | If all zeros satisfy beta<=Theta (1/2<=Theta<1), the same holds with x^Theta | `NTKB.Davenport.psi_sub_self_le_of_re_le` | proved |  |
| 18-11 | 124 | Converse: psi(x) = x + O(x^a) with a<1 implies zeta has no zeros with Re s > a | `NTKB.Davenport.riemannZeta_zero_re_le_of_psi` | proved |  |
| 18-12 | 124 | Identity -zeta'(s)/zeta(s) = s/(s-1) + s int_1^infty (psi(x)-x) x^(-s-1) dx for sigma>1 | `NTKB.Davenport.neg_logDeriv_riemannZeta_eq_integral` | proved |  |
| 18-13 | 124 | If psi(x)=x+O(x^(Theta+eps)) for all eps>0 with 1/2<=Theta<1 then psi(x)=x+O(x^Theta log^2 x) (Grosswald: log factor can be removed when Theta>1/2) | `NTKB.Davenport.psi_sub_self_le_of_forall_eps` | proved in part |  |

## Chapter 19: The explicit formula for psi(x, chi) (book pp. 115-120; pdf pp. 125-130)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 19-1 | 125 | Definition psi(x,chi) = sum over n<=x of chi(n) Lambda(n), with psi_0(x,chi) the midpoint-modified version at prime powers | `NTKB.psiL`, `NTKB.psi0L` | proved |  |
| 19-2 | 125 | For chi primitive and odd, psi_0(x,chi) = - sum_rho x^rho/rho + (L'/L)(0,chi) - sum_{m>=1} x^(1-2m)/(2m-1) | `NTKB.Davenport.explicit_formula_psi0L_odd` | proved in part |  |
| 19-3 | 126 | For chi primitive and even, psi_0(x,chi) = - sum_rho x^rho/rho - log x - b(chi) + sum_{m>=1} x^(-2m)/(2m), where L'/L(s,chi) = 1/s + b + ... near 0 | `NTKB.Davenport.explicit_formula_psi0L_even`, `NTKB.Davenport.tendsto_sum_L_zeros`, `NTKB.trivialSumL`, `NTKB.trivialSumL_odd`, `NTKB.trivialSumL_even` | proved in part |  |
| 19-4 | 126 | Unsymmetric functional equation L(1-s, chi-bar) = eps(chi) (2 pi / q)^(-s)... cos(pi (s-a)/2) Gamma(s) L(s,chi), with absolute value of eps equal to 1 | `ZMod.LFunction_one_sub`, `DirichletCharacter.completedLFunction_one_sub` | partly in other libraries; not proved here |  |
| 19-5 | 126 | L'/L(s,chi) = O(log(q abs(s))) for sigma<=-1 away from discs of radius 1/2 about the trivial zeros | `NTKB.Davenport.norm_logDeriv_LFunction_left_le`, `NTKB.logDeriv_dirichletXi_one_sub`, `NTKB.logDeriv_dirichletXi_eq` | proved in part |  |
| 19-6 | 127 | (D) finite formula: psi(x,chi) = - sum over abs(gamma)<T of x^rho/rho - (1-a) log x - b(chi) + sum x^(a-2m)/(2m-a) + R(x,T), where (E) R << x log^2(qxT)/T + log x min(1, x/(T<x>)) | `NTKB.residueZeroL`, `NTKB.Davenport.explicit_formula_psi0L`, `NTKB.Davenport.hasSum_explicitJL`, `NTKB.Davenport.norm_psi0L_sub_explicitJL_le`, `NTKB.Davenport.rectIntegral_explicitIntegrandL`, `NTKB.Davenport.norm_explicitJL_sub_main_le`, `NTKB.Davenport.exists_good_height_L`, `NTKB.Davenport.norm_logDeriv_LFunction_good_line`, `NTKB.Davenport.explicit_formula_psi0L_exact`, `NTKB.Davenport.norm_explicitJL_sub_main_exact_le`, `NTKB.Davenport.norm_left_integral_sub_trivialSumL_le`, `NTKB.bddNear_explicitIntegrandL_trivial` | proved in part |  |
| 19-7 | 127 | (F) for x an integer R(x,T) << x T^(-1) log^2(qxT) | `NTKB.residueZeroL`, `NTKB.Davenport.explicit_formula_psi0L`, `NTKB.Davenport.hasSum_explicitJL`, `NTKB.Davenport.norm_psi0L_sub_explicitJL_le`, `NTKB.Davenport.rectIntegral_explicitIntegrandL`, `NTKB.Davenport.norm_explicitJL_sub_main_le`, `NTKB.Davenport.exists_good_height_L`, `NTKB.Davenport.norm_logDeriv_LFunction_good_line` | proved in part |  |
| 19-8 | 127 | (G) with T<x and absorbing minor terms: psi(x,chi) = - sum over abs(gamma)<T of x^rho/rho - b(chi) + R_1(x,T), with R_1 << x T^(-1) log^2(qx) | — | not formalized |  |
| 19-9 | 128 | b(chi) = O(log q) - sum over zeros with abs(gamma)<1 of 1/rho, from (17) of Sect. 12 | `NTKB.Davenport.norm_bChar_add_sum_le`, `NTKB.bChar`, `NTKB.bChar_eq_odd`, `NTKB.bChar_eq_even` | proved |  |
| 19-10 | 128 | (9) psi(x,chi) = - sum over abs(gamma)<T of x^rho/rho + sum over abs(gamma)<1 of 1/rho + R_2(x,T) with R_2 << x T^(-1) log^2(qx) | `NTKB.Davenport.explicit_formula_psi0L'` | proved in part |  |
| 19-11 | 128 | Exceptional zero: for chi nonprincipal there is no zero with abs(gamma)<1, beta>1-c/log q unless chi is real, in which case there is at most one, simple and real, called beta_1 (and 1-beta_1 is also a zero) | `NTKB.Davenport.exceptional_zero_real`, `NTKB.IsExcPoint` | proved in part |  |
| 19-12 | 129 | (11) psi(x,chi) = - x^(beta_1)/beta_1 - sum' over abs(gamma)<T, excluding beta_1 and 1-beta_1, of x^rho/rho + R_3(x,T); (12) R_3 << x T^(-1) log^2(qx) + x^(1/2) log x | `NTKB.Davenport.psi0L_exceptional` | proved in part |  |
| 19-13 | 129 | The bound extends to imprimitive nonprincipal chi: psi(x,chi) and psi(x,chi_1) differ by at most (log x)(log q) | `NTKB.Davenport.norm_psiL_sub_primitive_le` | proved |  |
| 19-14 | 130 | (13),(14) restatement: for nonprincipal chi mod q and 2<=T<=x, psi(x,chi) = - x^(beta_1)/beta_1 - sum' x^rho/rho + R_3(x,T), R_3 << x T^(-1) log^2(qx) + x^(1/2) log x; the beta_1 term omitted unless chi is real with real zero > 1-c/log q; x^(1/2) log x term omittable when beta_1 absent | `NTKB.Davenport.psi0L_exceptional` | proved in part |  |
| 19-15 | 130 | At most one real character mod q can have a zero of L(s,chi) with beta>1-c/log q (from Sect. 14), so the exceptional zero is unique per modulus | — | not formalized |  |

## Chapter 20: The prime number theorem for arithmetic progressions (I) (book pp. 121-125; pdf pp. 131-135)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 20-1 | 131 | Definition psi(x;q,a) = sum of Lambda(n) over n<=x with n congruent to a mod q | `NTKB.Davenport.psiAP` | proved |  |
| 20-2 | 131 | (B) psi(x;q,a) = (1/phi(q)) sum over characters chi mod q of chi-bar(a) psi(x,chi) | `NTKB.Davenport.psiAP_eq` | proved | Mathlib: `ArithmeticFunction.vonMangoldt.residueClass_eq` |
| 20-3 | 131 | The principal character gives the main term: psi(x,chi_0) differs from psi(x) by at most (log q)(log x) | `NTKB.Davenport.norm_psiL_one_sub_psi_le` | proved |  |
| 20-4 | 132 | (8) For q<=exp(C sqrt(log x)) and nonprincipal chi mod q, psi(x,chi) = - x^(beta_1)/beta_1 + O(x exp(-C' sqrt(log x))) | `NTKB.Davenport.psi0L_sub_exceptional_le` | proved in part |  |
| 20-5 | 133 | (9) psi(x;q,a) = x/phi(q) - chi_1(a) x^(beta_1)/(phi(q) beta_1) + O(x exp(-C' sqrt(log x))) uniformly for q<=exp(C sqrt(log x)), chi_1 the single exceptional real character | `NTKB.Davenport.psiAP_sub_le` | proved in part |  |
| 20-6 | 133 | Only bound known for beta_1 here is beta_1 < 1 - c/(sqrt(q) log^2 q) (A12 of Sect. 14), giving the exceptional term size x/(phi(q)) exp(-c log x / (sqrt q log^2 q)) | — | not formalized |  |
| 20-7 | 133 | (11) If q<=(log x)^(1-delta) for fixed delta>0, then psi(x;q,a) = x/phi(q) + O(x exp(-c_4 sqrt(log x))) with effective constants | — | not formalized |  |
| 20-8 | 133 | Page's theorem consequence: for z=exp(C sqrt(log x)) there is at most one real primitive character of modulus <=z with beta > 1 - c_20/log z; call its modulus q_1 | `NTKB.IsPageModulus`, `NTKB.Davenport.isPageModulus_unique` | proved |  |
| 20-9 | 134 | (12) q_1 log^2 q_1 > log x (if q_1 exists, from beta_1 > 1 - c/(C sqrt(log x)) combined with A12 of Sect. 14) | — | not formalized |  |
| 20-10 | 134 | (13) Unless q is a multiple of q_1(x), psi(x;q,a) = x/phi(q) + O(x exp(-C'' sqrt(log x))) uniformly for q<=exp(C sqrt(log x)) | `NTKB.Davenport.psiAP_sub_le_page` | proved |  |
| 20-11 | 134 | Generalized Riemann hypothesis: all L(s,chi) have their nontrivial zeros on Re s=1/2 | `NTKB.GeneralizedRiemannHypothesis` | proved |  |
| 20-12 | 134 | Under GRH and q<x, psi(x,chi_0) = x + O(x^(1/2) log^2 x) | `NTKB.Davenport.psiAP_sub_le_of_GRH` | proved |  |
| 20-13 | 135 | Under GRH, for nonprincipal chi mod q<x: psi(x,chi) << x^(1/2) log^2(qx) taking T=x^(1/2); uses sum of 1/abs(rho) << log^2(qx) over abs(gamma)<T | `NTKB.Davenport.norm_psi0L_le_of_GRH` | proved |  |
| 20-14 | 135 | (14) Under GRH, psi(x;q,a) = x/phi(q) + O(x^(1/2) log^2 x) for q<x | `NTKB.Davenport.psiAP_sub_le_of_GRH` | proved |  |
| 20-15 | 131 | Analog statements for pi(x;q,a): main term li(x)/phi(q) and error terms smaller by log x, via partial summation (stated in Sect. 22) | — | not formalized |  |

## Chapter 21: Siegel's theorem (book pp. 126-131; pdf pp. 136-141)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 21-1 | 136 | Siegel's theorem, first form: for every eps>0 there is C_1(eps)>0 with L(1,chi) > C_1(eps) q^(-eps) for every real primitive character chi mod q | — | not formalized |  |
| 21-2 | 136 | (B) h(d) > C_2(eps) times abs(d)^(1/2-eps) for d<0 | — | not formalized |  |
| 21-3 | 136 | (C) h(d) log(eta) > C_2(eps) d^(1/2-eps) for d>0, eta the fundamental unit | — | not formalized |  |
| 21-4 | 136 | Second form: for every eps>0 there is C_3(eps)>0 such that L(s,chi) != 0 for s > 1 - C_3(eps) q^(-eps), chi any real nonprincipal character mod q | — | not formalized |  |
| 21-5 | 137 | (E) Every real zero beta of L(s,chi), chi real nonprincipal, satisfies beta < 1 - C_3(eps) q^(-eps) | — | not formalized |  |
| 21-7 | 137 | Hecke: if real zeros satisfy beta<1-c/log q then h(d) > c sqrt(abs(d)) / log(abs(d)) for d<0 (so GRH gives h(d)->infinity) | — | not formalized |  |
| 21-8 | 137 | Deuring/Mordell/Heilbronn: h(d)->infinity as d->-infinity (Gauss' problem), in the cases of falsity of RH or of GRH | — | not formalized |  |
| 21-9 | 137 | Heilbronn-Linfoot 1934: at most ten negative discriminants d with h(d)=1 | — | not formalized |  |
| 21-10 | 138 | Baker 1966, Stark 1966-67 (Heegner 1952): the nine discriminants -3,-4,-7,-8,-11,-19,-43,-67,-163 are the only negative d with class number 1 | `classNumber_neg_eq_one_of_mem_heegnerDiscriminants` | partly in other libraries; not proved here |  |
| 21-11 | 138 | Baker and Stark have found all negative discriminants with h(d)=2; h(d)=3 remains open (as of the book) | — | not formalized |  |
| 21-12 | 138 | (F) F(s)=zeta(s) L(s,chi_1) L(s,chi_2) L(s,chi_1 chi_2) is regular except for a simple pole at s=1 (chi_1, chi_2 real primitive to distinct moduli q_1, q_2) | — | not formalized |  |
| 21-13 | 138 | (G) Residue of F at s=1 is A = L(1,chi_1) L(1,chi_2) L(1,chi_1 chi_2) | — | not formalized |  |
| 21-14 | 138 | (8) Siegel-type inequality: F(sigma) > 1 - c A (q_1 q_2)^(c(1-sigma)) / (1-sigma) for 1/2<sigma<1 (c an absolute constant; exact form garbled in OCR) | — | not formalized |  |
| 21-15 | 139 | F(s) = sum a_n n^(-s) with a_1=1 and a_n>=0, since log F has nonnegative Dirichlet coefficients | — | not formalized |  |
| 21-16 | 139 | F(s) = sum_{m>=0} b_m (2-s)^m for abs(s-2)<1, with b_0>=1 and b_m>=0; the series for F(s)-A/(s-1) is valid for abs(s-2)<2 | — | not formalized |  |
| 21-17 | 139 | (10) The Taylor coefficients satisfy a bound of the form abs(b_m - A) <= 2 c_5 (q_1 q_2)^c (2/3)^m (Cauchy's inequalities on the circle abs(s-2)=3/2, using the polynomial bound of L(s,chi) in q from (14) of Sect. 12) | — | not formalized |  |
| 21-18 | 140 | Case analysis (Estermann): if some real primitive chi has a real zero in (1-eps/c,1), take it as chi_1 and that zero as beta_1; otherwise take any chi_1 and beta_1 in that range; in both cases F(beta_1)<=0 | — | not formalized |  |
| 21-19 | 141 | Conclusion: with chi_1, beta_1 fixed, for any real primitive chi_2 mod q_2>q_1, L(1,chi_2) >> C(eps) (q_2)^(-eps), proving Siegel's theorem | — | not formalized |  |
| 21-20 | 140 | The first form follows from the second by Landau's argument (footnote) | — | not formalized |  |

## Chapter 22: The prime number theorem for arithmetic progressions (II) (book pp. 132-134; pdf pp. 142-144)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 22-1 | 142 | For q<=(log x)^N and nonprincipal chi mod q, using Siegel with eps=1/(2N): psi(x,chi) << x exp(-C_3(N) sqrt(log x)) | — | not formalized |  |
| 22-2 | 143 | Siegel-Walfisz theorem: for any N there is C_4(N)>0 with psi(x;q,a) = x/phi(q) + O(x exp(-C_4(N) sqrt(log x))) uniformly for q<=(log x)^N, (a,q)=1 | — | not formalized |  |
| 22-3 | 143 | Analogs for pi(x;q,a): main term li(x)/phi(q), error terms reduced by log x by partial summation as in Sect. 18 | — | not formalized |  |
| 22-4 | 143 | (E) Retaining the exceptional term: psi(x;q,a) = x/phi(q) - chi_1(a) x^(beta_1)/(phi(q) beta_1) + O(...), chi_1 the possible exceptional real character | — | not formalized |  |
| 22-5 | 143 | Rodosskii and Tatuzawa (building on Linnik): estimates for the sum over chi mod q of N(alpha,T,chi), giving a better error in 22-4 or a longer q range | — | not formalized |  |
| 22-6 | 144 | Renyi: for primes q<=(log N)... pi(x;q,a) - li(x)/phi(q) bound with at most N^(1/2) log N exceptional q and q^(1/2) exceptional a per q | — | not formalized |  |
| 22-7 | 144 | Bombieri: for any A>0 there is B>0 with the sum over q<=Q of the max over (a,q)=1 and y<=x of the absolute value of psi(y;q,a) - y/phi(q) << x (log x)^(-A) whenever Q = x^(1/2) (log x)^(-B) | — | not formalized |  |

## Chapter 23: The Polya-Vinogradov Inequality (book pp. 135-137; pdf pp. 145-147)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 23-1 | 145 | Polya-Vinogradov: for a nonprincipal character chi mod q, every incomplete sum of chi(n) over M<n<=M+N has absolute value at most a constant times sqrt(q) log q | `NTKB.Davenport.norm_sum_Ioc_le`, `NTKB.Davenport.norm_sum_Ioc_lt_of_isPrimitive` | proved |  |
| 23-2 | 145 | Corollary: an interval of length N contains N/2 + O(sqrt(p) log p) quadratic residues mod p (Legendre symbol case of 23-1) | `NTKB.Davenport.abs_two_mul_card_residues_sub_le` | proved |  |
| 23-4 | 145 | Gauss sum identity for primitive chi (from section 9): chi(n) tau(conj chi) equals the sum over a of conj chi(a) e(an/q), with abs(tau(chi)) = sqrt(q) | `NTKB.Davenport.char_mul_gaussSum_inv` | proved | Mathlib: `gaussSum_mulShift_of_isPrimitive`, Tau Ceti: `DirichletCharacter.IsPrimitive.norm_gaussSum` |
| 23-5 | 146 | Geometric-series step: for primitive chi the sum of chi(n) over an interval is bounded by q^(-1/2) times the sum over a of abs(sin(pi N a/q) / sin(pi a/q)) | `NTKB.Davenport.norm_sum_Ioc_le_of_isPrimitive`, `NTKB.Davenport.norm_sum_Ioc_exp` | proved |  |
| 23-6 | 146 | Averaging lemma for convex f: f(alpha) is at most (1/(2 delta)) times the integral of f over (alpha-delta, alpha+delta), applied with f = 1/sin(pi a) and delta = 1/q | `NTKB.Davenport.le_average_integral_of_convexOn`, `NTKB.Davenport.sum_one_div_sin_lt_mul_log` | proved |  |
| 23-7 | 146 | Inequality (B): for primitive chi mod q>1, the interval sum of chi has absolute value less than sqrt(q) log q | `NTKB.Davenport.norm_sum_Ioc_le`, `NTKB.Davenport.norm_sum_Ioc_lt_of_isPrimitive` | proved |  |
| 23-8 | 146 | Reduction to the primitive case: if chi mod q is induced by chi1 mod q1 with q = q1 r, then the sum of chi equals a Moebius-weighted sum over d dividing r of chi1(d) times interval sums of chi1 | `NTKB.Davenport.sum_Ioc_changeLevel_eq` | proved |  |
| 23-9 | 147 | Divisor bounds finishing the proof: 2^omega(r) <= d(r) <= 2 sqrt(r), giving the sqrt(q) log q bound in 23-1 for imprimitive chi | `NTKB.Apostol.card_divisors_le_two_sqrt`, `NTKB.Davenport.norm_sum_Ioc_le` | proved |  |
| 23-10 | 147 | Schur: for primitive chi mod q the maximum over N of the partial sum up to N has absolute value at least sqrt(q)/(2 pi) | — | not formalized |  |
| 23-11 | 147 | Paley: for infinitely many quadratic discriminants d>0 the maximal partial sum of the quadratic character exceeds a constant times sqrt(d) log log d | — | not formalized |  |
| 23-12 | 147 | Montgomery-Vaughan: under GRH, every interval sum of a nonprincipal chi is O(sqrt(q) log log q) | — | not formalized |  |

## Chapter 24: Further Prime Number Sums (book pp. 138-142; pdf pp. 148-152)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 24-1 | 148 | Vinogradov sieve identity: with P the product of primes up to sqrt(N), the sum of f(p) over primes in (sqrt N, N] equals the sum over t dividing P of mu(t) times the sum of f(rt) over r<=N/t, minus f(1) | — | not formalized |  |
| 24-2 | 148 | Vaughan identity (1): -zeta'/zeta = F - zeta F G - zeta' G + (-zeta'/zeta - F)(1 - zeta G) for Re s>1, with F the truncated Lambda series (m<=U) and G the truncated mu series (d<=V) | `NTKB.Davenport.vaughan_identity_LSeries` | proved |  |
| 24-3 | 149 | Coefficient form of Vaughan identity: Lambda(n) = a1(n)+a2(n)+a3(n)+a4(n) with a1 the truncation of Lambda to n<=U, a2 = minus sum over mdr=n of Lambda(m)mu(d), a3 = sum over hd=n of mu(d) log h, a4 = minus sum over mk=n of Lambda(m) times a divisor sum of mu | `NTKB.Davenport.vaughan_identity`, `NTKB.Davenport.one_sub_zeta_mul_trunc`, `NTKB.Davenport.one_sub_zeta_mul_trunc_of_lt`, `NTKB.Davenport.zeta_mul_truncate_apply`, `NTKB.Davenport.truncate` | proved |  |
| 24-4 | 149 | Decomposition: the sum of f(n)Lambda(n) over n<=N equals S1+S2+S3+S4, with S1 trivially at most U (sizes) | `NTKB.Davenport.sum_mul_vonMangoldt_eq`, `NTKB.Davenport.S₄_eq` | proved |  |
| 24-5 | 149 | Type I bound (B): S2 is at most (log UV) times the sum over t<=UV of abs(sum of f(rt) over r<=N/t) | `NTKB.Davenport.norm_S₂_le`, `NTKB.Davenport.abs_trunc_mul_trunc_le`, `NTKB.Davenport.sum_mul_sum_divisors` | proved |  |
| 24-6 | 150 | Type I bound (C): S3 is at most (log N) times the sum over d<=V of the max over w of abs(sum of f(dh) over w<=h<=N/d), via partial summation | `NTKB.Davenport.norm_S₃_le`, `NTKB.Davenport.norm_sum_mul_log_le` | proved |  |
| 24-8 | 150 | Type II bound (E): S4 is O(N^(1/2) (log N)^c max A) where the max is over U<M<=N/V and A is the constant in (D) | `NTKB.Davenport.norm_S₄_le` | proved in part |  |
| 24-9 | 150 | Elementary mean-square bounds: the sum of Lambda(m)^2 over m<=z is O(z log z) and the sum of d(k)^2 over k<=z is O(z (log 2z)^3) | `NTKB.Davenport.sum_vonMangoldt_sq_le`, `NTKB.Davenport.sum_card_divisors_sq_le` | proved in part |  |
| 24-11 | 151 | Reduction of A by Cauchy-Schwarz: A^2 is at most a constant times the max over j of the sum over k of abs(sum over m of f(mj) conj f(mk)) | `NTKB.Davenport.norm_bilinear_sq_le` | proved |  |
| 24-12 | 152 | Vinogradov-Vaughan estimate (F): for abs(f)<=1, U,V>=2, UV<=N, the sum of f(n)Lambda(n) over n<=N is O(U) plus (log N) times the sum over t<=UV of max_w abs(sum f(rt)) plus N^(1/2) (log N)^c times a max over M,j of the square root of the sum over k of abs(sum over m of f(mj) conj f(mk)) | `NTKB.Davenport.norm_sum_mul_vonMangoldt_le` | proved in part |  |

## Chapter 25: An Exponential Sum Formed with Primes (book pp. 143-144; pdf pp. 153-154)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 25-2 | 153 | Vinogradov estimate (2): if abs(alpha - a/q) <= 1/q^2 with (a,q)=1 then S(alpha) = O((N q^(-1/2) + N^(4/5) + N^(1/2) q^(1/2)) (log N)^4) | `NTKB.Davenport.norm_sum_vonMangoldt_exp_le` | proved |  |
| 25-3 | 153 | Geometric sum bound: the sum of e(n beta) over N1<n<=N2 is O(min(N2-N1, 1/distance of beta to nearest integer)) | `NTKB.Davenport.norm_sum_Icc_exp_le` | proved |  |
| 25-4 | 153 | Reduction: the sum over t<=T of max_w abs(sum of e(rt alpha) over w<=r<=N/t) is O(sum over t<=T of min(N/t, 1/norm(t alpha))) | `NTKB.Davenport.norm_sum_vonMangoldt_exp_le`, `NTKB.Davenport.vino_row_sum` | proved |  |
| 25-5 | 154 | Estimate (3): for alpha as in (1), the sum over t<=T of min(N/t, 1/norm(t alpha)) is O((N/q + T + q) log 2qT) | `NTKB.Davenport.sum_minInv_le`, `NTKB.Davenport.distInt`, `NTKB.Davenport.minInv` | proved |  |
| 25-6 | 154 | Combination: S(alpha) = O((UV + q + N U^(-1/2) + N V^(-1/2) + N q^(-1/2) + N^(1/2) q^(1/2)) (log qN)^4), then take U=V=N^(2/5) | `NTKB.Davenport.norm_sum_vonMangoldt_exp_le` | proved |  |

## Chapter 26: Sums of Three Primes (book pp. 145-150; pdf pp. 155-160)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 26-2 | 155 | Truncated count r'(n) (same as r(n) with all k_i<=N) satisfies S(alpha)^3 = sum of r'(n) e(n alpha), and r'(n) = r(n) for n<=N | — | not formalized |  |
| 26-3 | 155 | Fourier coefficient formula (1): r(N) equals the integral over [0,1] of S(alpha)^3 e(-N alpha) d alpha | — | not formalized |  |
| 26-4 | 156 | Vinogradov's theorem: for fixed A>0, r(N) = (1/2) G(N) N^2 + O(N^2 (log N)^(-A)), where G(N) is the product over p dividing N of (1 - 1/(p-1)^2) times the product over p not dividing N of (1 + 1/(p-1)^3) | — | not formalized |  |
| 26-5 | 156 | Consequence: for odd N, G(N) >> 1 so r(N) >> N^2; proper prime powers contribute O(N^(3/2) (log N)^2); hence every sufficiently large odd N is a sum of three primes in >> N^2 (log N)^(-3) ways (for even N, G(N)=0) | — | not formalized |  |
| 26-7 | 156 | Orthogonality over characters mod q: (1/phi(q)) times the sum over chi of tau(conj chi) chi(h) equals e(h/q) if (h,q)=1 and 0 otherwise | `gaussSum_mulShift_of_isPrimitive`, `DirichletCharacter.sum_char_inv_mul_char_eq` | partly in other libraries; not proved here |  |
| 26-8 | 157 | Formula (B): on a major arc alpha = a/q + beta, S(alpha) = (1/phi(q)) sum over chi of tau(conj chi) chi(a) times the sum of chi(k)Lambda(k)e(k beta), plus O((log N)^2) | — | not formalized |  |
| 26-9 | 157 | The twisted sum of chi(k)Lambda(k)e(k beta) equals e(N beta) psi(N,chi) minus 2 pi i beta times an integral of e(u beta) psi(u,chi) du (partial summation) | — | not formalized |  |
| 26-10 | 157 | For nonprincipal chi the twisted sum is O((1+N abs(beta)) N exp(-c sqrt(log N))) by the PNT in progressions (estimate (C) of section 22, Siegel-based) | — | not formalized |  |
| 26-11 | 157 | On a major arc, S(alpha) = (mu(q)/phi(q)) T(beta) + O((1+N abs(beta)) N exp(-c sqrt(log N))) with T(beta) = sum over k<=N of e(k beta); hence S(alpha)^3 is (mu(q)/phi(q))^3 T(beta)^3 plus a small error | — | not formalized |  |
| 26-12 | 158 | Major arc contribution (D): the integral over M is the sum over q<=P, (a,q)=1 of (mu(q)/phi(q))^3 c_q(-N) times an integral of T(beta)^3 e(-N beta) over abs(beta)<=1/Q, plus O(N^2 exp(-c sqrt(log N))) | — | not formalized |  |
| 26-13 | 158 | Evaluation (E): the integral of T(beta)^3 e(-N beta) over abs(beta)<=1/Q equals N^2/2 + O(N^2 (log N)^(-B)), via counting representations N = k1+k2+k3 (number is (N-1)(N-2)/2) | — | not formalized |  |
| 26-14 | 158 | Ramanujan sum formula (F): c_q(n), the sum of e(an/q) over a mod q with (a,q)=1, equals the sum over d dividing (q,n) of d mu(q/d) | — | not formalized |  |
| 26-15 | 159 | c_q(n) is multiplicative in q and c_q(n) = mu(q/(n,q)) phi(q)/phi(q/(n,q)); in particular abs(c_q(n)) <= phi(q) | — | not formalized |  |
| 26-16 | 159 | Singular series: the sum over all q of mu(q) c_q(N)/phi(q)^3 converges absolutely and equals the Euler product G(N) above; the tail over q>P is small (a negative power of log N) | — | not formalized |  |
| 26-18 | 160 | Parseval for S: the integral over [0,1] of abs(S(alpha))^2 equals the sum of Lambda(k)^2 over k<=N, which is at most N log N | `NTKB.Davenport.integral_norm_sum_exp_sq` | proved in part | Mathlib: `tsum_sq_fourierCoeff` |
| 26-19 | 160 | Dirichlet's approximation theorem: for real alpha and real Q>1 there is a reduced fraction a/q with abs(alpha - a/q) < 1/(qQ), q<=Q | `Real.exists_rat_abs_sub_le_and_den_le` | in Mathlib |  |
| 26-20 | 160 | Minor arc estimate: for alpha in m, section 25 gives abs(S(alpha)) << N (log N)^(-B/2+c), hence the minor-arc integral is O(N^2 (log N)^(-B/2+c')); choosing B = 2A + 10 completes the theorem | — | not formalized |  |

## Chapter 27: The Large Sieve (book pp. 151-160; pdf pp. 161-170)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 27-1 | 161 | Bessel inequality: for orthonormal phi_1..phi_R and any xi, the sum of abs((xi,phi_r))^2 is at most norm(xi)^2 | `Orthonormal.sum_inner_products_le`, `Orthonormal.tsum_inner_products_le`, `NTKB.Davenport.sum_norm_inner_sq_le_of_orthonormal` | in Mathlib |  |
| 27-3 | 161 | Boas: inequality (A) holds for all xi if and only if the bilinear form inequality (B) holds: abs of the sum over r,s of u_r conj u_s (phi_r,phi_s) is at most A times the sum of abs(u_r)^2 for all complex u | `NTKB.Davenport.boas_iff` | proved |  |
| 27-4 | 163 | Almost-orthogonal Bessel inequality: in an inner product space, the sum over r of abs((xi,phi_r))^2 is at most A norm(xi)^2 with A = max over r of the sum over s of abs((phi_r,phi_s)); equals Bessel when the phi_r are orthonormal (A=1). Mathlib has only the orthonormal case | `NTKB.Davenport.sum_norm_inner_sq_le` | proved | Mathlib: `Orthonormal.tsum_inner_products_le` |
| 27-6 | 164 | Lower bounds for A: for a single point equality in Cauchy-Schwarz gives A >= N; averaging over shifts beta of R = floor(1/delta) points gives A >= 1/delta - 1 | — | not formalized |  |
| 27-7 | 164 | Large sieve (Theorem 2): for delta-separated points alpha_1..alpha_R mod 1 and S as above, the sum of abs(S(alpha_r))^2 is at most (N + 3/delta) times the sum of abs(a_n)^2 | `NTKB.Davenport.large_sieve` | proved |  |
| 27-8 | 165 | Fejer-type identity: the sum over abs(j)<J of (J-abs(j)) e(j alpha) equals (sin(pi J alpha)/sin(pi alpha))^2, used to build the smooth weights b_k (1 for abs(k)<=K, linear decay over L) with closed form hat b(alpha) | `NTKB.Davenport.sum_fejer_eq`, `NTKB.Davenport.norm_sum_range_exp_sq` | proved |  |
| 27-9 | 166 | Weight estimates: hat b(0) = 2K+L, abs(hat b(alpha)) <= 1/(4 L norm(alpha)^2), and sum of 1/h^2 <= 2 (Davenport notes it equals zeta(2) = pi^2/6); choose L = least integer >= 1/delta to get inequality (G) with bound 2K + 3/delta | `NTKB.Davenport.sum_sieveWeight`, `NTKB.Davenport.norm_sum_sieveWeight_le`, `NTKB.Davenport.sum_norm_sieveWeight_le`, `NTKB.Davenport.sum_Icc_inv_sq_le_two` | proved | Mathlib: `hasSum_zeta_two` |
| 27-10 | 166 | Selberg's sharper constant: choosing the weights more carefully gives A = N + 1/delta - 1 | — | not formalized |  |
| 27-11 | 166 | Gallagher's lemma: for f with continuous derivative, abs(f(alpha)) is at most (1/(2 delta)) times the integral of abs(f) over (alpha-delta, alpha+delta) plus half the integral of abs(f') | `NTKB.Davenport.norm_le_integral_norm_add_integral_norm_deriv` | proved |  |
| 27-12 | 167 | Gallagher's large sieve constant: A = pi N + 1/delta, obtained by applying 27-11 to f = S^2 and using Parseval for S and S' | `NTKB.Davenport.large_sieve_gallagher` | proved |  |
| 27-13 | 167 | Parseval for trigonometric polynomials: the integral over [0,1] of abs(S(alpha))^2 equals the sum of abs(a_n)^2 | `NTKB.Davenport.integral_norm_sum_exp_sq` | proved in part | Mathlib: `tsum_sq_fourierCoeff` |
| 27-14 | 167 | Farey form (8): for Q>=1 the sum over q<=Q and a mod q with (a,q)=1 of abs(S(a/q))^2 is at most (N + 3Q^2) times the sum of abs(a_n)^2 | `NTKB.Davenport.large_sieve_farey` | proved |  |
| 27-15 | 168 | Renyi form: Z integers in an interval of length N, Z(q,h) their count in class h mod q, V(q) the variance of Z(q,h); then the sum over primes p<=Q of p V(p) is at most (N + 3Q^2) Z | `NTKB.Davenport.sum_prime_mul_variance_le` | proved |  |
| 27-16 | 168 | Identity: q V(q) equals the sum over a=1..q-1 of abs(S(a/q))^2 where S has a_n the indicator of the set | `NTKB.Davenport.mul_variance_eq` | proved |  |
| 27-17 | 169 | Sieve form of the large sieve (Theorem 3): a set of Z integers in (M, M+N] such that for each p in a set of P primes up to Q it misses at least tau p residue classes mod p satisfies Z <= (N + 3Q^2)/(tau P) | `NTKB.Davenport.card_le_of_sieve` | proved |  |
| 27-19 | 169 | Montgomery's refinement: Z <= (N + 3Q^2)/L with L the sum over q<=Q of mu(q)^2 times the product over p dividing q of omega(p)/(p - omega(p)), omega(p) the number of missed classes mod p (earlier Bombieri-Davenport special case) | — | not formalized |  |
| 27-20 | 170 | Gallagher's large sieve for characters (Theorem 4): for Q>=1 the sum over q<=Q of q/phi(q) times the sum over primitive chi mod q of abs(sum of a_n chi(n))^2 is at most (N + 3Q^2) times the sum of abs(a_n)^2 | `NTKB.Davenport.large_sieve_characters` | proved |  |
| 27-21 | 170 | Reduction (10): for the character sums T(chi), the sum over primitive chi of abs(T(chi))^2 is at most phi(q)/q times the sum over a mod q coprime to q of abs(S(a/q))^2; uses chi(n) = (1/tau(conj chi)) sum conj chi(a) e(an/q) and abs(tau)^2 = q, then extends to all chi and orthogonality | `NTKB.Davenport.sum_primitive_norm_sq_le`, `NTKB.Davenport.sum_char_norm_sq` | proved | Mathlib: `gaussSum_mulShift_of_isPrimitive`, Mathlib: `DirichletCharacter.sum_char_inv_mul_char_eq` |

## Chapter 28: Bombieri's Theorem (book pp. 161-168; pdf pp. 171-178)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 28-2 | 171 | Bombieri's theorem: for fixed A>0, the sum over q<=Q of E*(x,q) is O(x^(1/2) Q (log x)^5) provided x^(1/2) (log x)^(-A) <= Q <= x^(1/2) | — | not formalized |  |
| 28-3 | 172 | Strength remarks: trivially E*(x,q) << x log x / q, so the sum is trivial for Q<=x^(1/2) up to log powers; the theorem gives psi(x;q,a) = x/phi(q) (1 + O((log x)^(-A))) for all (a,q)=1 and all q<=Q except O(Q (log x)^(-A)) values of q (Q = x^(1/2) (log x)^(-2A-5)) | — | not formalized |  |
| 28-5 | 172 | Key estimate (B), reduction target: the sum over q<=Q of q/phi(q) times the sum over primitive chi mod q of max over y<=x of abs(psi'(y,chi)) is O((x + x^(5/6) Q + x^(1/2) Q^2) (log Qx)^c) for all x,Q>=1, where psi' removes the main term y for the principal character | `NTKB.Davenport.sum_psiChar'_le`, `NTKB.Davenport.sum_supPsi_le`, `NTKB.Davenport.supPsi` | proved |  |
| 28-6 | 172 | Formula and bound: E(y;q,a) = (1/phi(q)) times the sum over chi of conj chi(a) psi'(y,chi), hence E(y;q) <= (1/phi(q)) sum over chi of abs(psi'(y,chi)) | `NTKB.Davenport.psiAP_sub_eq`, `NTKB.Davenport.psiAP`, `NTKB.Davenport.psiChar`, `NTKB.Davenport.psiChar'`, `NTKB.Davenport.abs_psiAP_sub_le` | proved in part | Mathlib: `DirichletCharacter.sum_char_inv_mul_char_eq` |
| 28-7 | 173 | Passing from chi mod q to its inducing primitive chi1: psi'(y,chi1) - psi'(y,chi) is O((log qy)^2), so E*(x,q) <= (log qx)^2 + (1/phi(q)) times the sum over chi of max abs(psi'(y,chi1)) | `NTKB.Davenport.norm_psiChar'_sub_le`, `NTKB.Davenport.abs_psiAP_sub_le` | proved in part |  |
| 28-8 | 173 | Collecting characters by their primitive inducing character, using phi(kq) >= phi(k)phi(q) and sum over k<=z of 1/phi(k) being O(log z), the theorem reduces to estimate (C): the sum over q<=Q of (1/phi(q)) times the sum over primitive chi of max over y<=x of abs(psi'(y,chi)) is O(x^(1/2) Q (log x)^c) for x^(1/2)(log x)^(-A) <= Q <= x^(1/2) | `NTKB.Davenport.sum_sum_primitiveCharacter_le`, `NTKB.Davenport.sum_inv_totient_mul_le`, `NTKB.Davenport.sum_inv_totient_le`, `NTKB.Davenport.totient_mul_totient_le`, `NTKB.Davenport.sum_abs_psiAP_sub_le`, `NTKB.Davenport.sum_inv_totient_supPsi_le` | proved, conditional |  |
| 28-9 | 174 | Small moduli: for primitive chi mod q with q<=(log x)^d and y<=x, psi'(y,chi) << x (log x)^(-A) (estimate (C) of section 22), so such q contribute acceptably to (C); large q in dyadic ranges U<q<=2U are handled by (B) | `NTKB.Davenport.SiegelWalfiszHypothesis.supPsi_le`, `NTKB.Davenport.sum_div_le_of_sum_le` | proved, conditional |  |
| 28-10 | 174 | Large sieve consequence (D) of Theorem 4 (restated): sum over q<=Q of q/phi(q) times the sum over primitive chi of abs(sum of a_n chi(n))^2 is at most (N + 3Q^2) times the sum of abs(a_n)^2 | `NTKB.Davenport.large_sieve_characters` | proved |  |
| 28-11 | 174 | Bilinear estimate (E): the sum over q<=Q of q/phi(q) times the sum over primitive chi of the max over u of abs of the double sum of a_m b_n chi(mn) over m<=M, n<=N, mn<=u is O(((M+Q^2)(N+Q^2))^(1/2) (sum abs(a_m)^2)^(1/2) (sum abs(b_n)^2)^(1/2) log 2MN) | `NTKB.Davenport.bilinear_sieve_sup`, `NTKB.Davenport.bilinear_large_sieve` | proved |  |
| 28-12 | 175 | Truncated Perron integral (lemma of section 17, c -> 0): the integral over (-T,T) of e^(i t alpha) sin(t beta)/t dt is pi plus O(1/(T(beta-abs(alpha)))) if abs(alpha)<beta, and O(1/(T(abs(alpha)-beta))) if abs(alpha)>beta; applied with beta = log u | `NTKB.Davenport.perron_truncated_sine`, `NTKB.Davenport.sineInt_error_pi_div_two` | proved |  |
| 28-13 | 176 | Proof of (E) completed: with T = (MN)^(1/2) the weight becomes min(1/abs(t), log 2MN) and the error terms are absorbed | `NTKB.Davenport.bilinear_sieve_sup`, `NTKB.Davenport.bilinear_large_sieve` | proved |  |
| 28-14 | 176 | Case Q^2>x of (B) follows from (E) with M=1, a_1=1, b_n=Lambda(n), N=x | `NTKB.Davenport.sum_psiChar_le_of_sq_ge` | proved |  |
| 28-15 | 176 | For Q^2<=x: Vaughan decomposition psi'(y,chi) = S1+S2+S3+S4 (explicit pieces (7)-(10) with chi inserted); S1 << U; S4 satisfies (11),(12): the sum over q<=Q of q/phi(q) times the sum over chi of max abs(S4) is O((Q^2 x^(1/2) + Q x U^(-1/2) + Q x V^(-1/2) + x)(log x)^4) | `NTKB.Davenport.norm_psi_prim_le`, `NTKB.Davenport.S₄_eq_bilinear`, `NTKB.Davenport.dyadic_bilinear_sieve`, `NTKB.Davenport.norm_S₁_le` | proved |  |
| 28-16 | 177 | Type I pieces: S2 split into S2' (t<=U) and S2'' (U<t<=UV); S2'' obeys (13) like S4; S2' is O(q^(1/2) U (log qU)^2) by Polya-Vinogradov (trivial bound x(log xU)^2 when q=1), giving (14) with Q^(1/2) U + x; S3 gives (15) with Q^(1/2) V + x | `NTKB.Davenport.norm_S₂'_le`, `NTKB.Davenport.S₂''_eq`, `NTKB.Davenport.norm_S₃_char_le`, `NTKB.Davenport.norm_sum_Icc_char_le` | proved |  |
| 28-17 | 177 | Combined bound: the left side of (B) is O((Q^2 x^(1/2) + x + QxU^(-1/2) + QxV^(-1/2) + U^(1/2) V^(1/2) Q x^(1/2) + Q^(1/2) U + Q^(1/2) V)(log xUV)^4); take U=V, with U = x^(1/2)/Q for x^(1/3)<=Q<=x^(1/2) and U = x^(1/3) for Q<=x^(1/3), giving (B) | `NTKB.Davenport.sum_psiChar'_le_UV`, `NTKB.Davenport.Z_bound_small`, `NTKB.Davenport.Z_bound_large` | proved |  |
| 28-19 | 178 | Zero-density estimate (Bombieri, improved by Montgomery): the sum over q<=Q of the sum over primitive chi of N(sigma,T,chi) is O(T(Q^2+QT)^(4(1-sigma)/(3-2 sigma)) (log QT)^10) | — | not formalized |  |
| 28-20 | 178 | Gallagher identity -L'/L = -(L'/L)(1-LG)^2 - 2L'G + L'LG^2 and Vaughan's identity (16): -L'/L = F - LFG - L'G + (-L'/L - F)(1 - LG); Vaughan's earlier bound for the same average is slightly weaker than (B) | — | not formalized |  |

## Chapter 29: An Average Result (book pp. 169-171; pdf pp. 179-181)

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| 29-1 | 179 | Barban-Davenport-Halberstam theorem (Gallagher's form), estimate (1): for fixed A>0 and x (log x)^(-A) < Q <= x, the sum over q<=Q and over a mod q coprime to q of (psi(x;q,a) - x/phi(q))^2 is O(x Q log x) | — | not formalized |  |
| 29-2 | 179 | Montgomery: the left side of (1) is asymptotic to Q x log x on that range (so (1) is best possible); Hooley combined this with (1) for a precise asymptotic | — | not formalized |  |
| 29-3 | 179 | Large sieve estimate (B), from Theorem 4 with a_n = Lambda(n): the sum over q<=Q of q/phi(q) times the sum over primitive chi mod q of abs(psi(x,chi))^2 is at most (x + Q^2) x log x | `NTKB.Davenport.sum_mul_sum_primitive_psiChar_le`, `NTKB.Davenport.sum_vonMangoldt_sq_le` | proved |  |
| 29-4 | 179 | Character expansion (C): psi(x;q,a) - x/phi(q) = (1/phi(q)) times the sum over chi of conj chi(a) psi'(x,chi) (psi' removes the main term for principal chi) | `NTKB.Davenport.psiAP_sub_eq`, `NTKB.Davenport.psiAP`, `NTKB.Davenport.psiChar`, `NTKB.Davenport.psiChar'` | proved | Mathlib: `DirichletCharacter.sum_char_inv_mul_char_eq` |
| 29-5 | 180 | Parseval over residue classes: the sum over a mod q coprime to q of abs(psi(x;q,a) - x/phi(q))^2 equals (1/phi(q)) times the sum over chi mod q of abs(psi'(x,chi))^2, by orthogonality of characters | `NTKB.Davenport.sum_sq_psiAP_sub_eq`, `NTKB.Davenport.sum_units_norm_sq` | proved | Mathlib: `DirichletCharacter.sum_char_inv_mul_char_eq` |
| 29-6 | 180 | Induced characters: if chi mod q is induced by primitive chi1, then psi'(x,chi) = psi'(x,chi1) + O((log qx)^2); so the main term of the sum reduces to primitive characters | `NTKB.Davenport.norm_psiChar'_sub_le` | proved |  |
| 29-7 | 180 | Grouping by inducing primitive character: the sum is dominated by the sum over q<=Q of (1/phi(q))-weighted primitive character sums times the sum over k<=Q/q of 1/phi(kq), which is O(phi(q)^(-1) log(2Q/q)); it suffices to show (C): the sum over q<=Q of (1/phi(q)) log(Q/q) times the sum over primitive chi of abs(psi'(x,chi))^2 is O(x Q log x) | `NTKB.Davenport.sum_sum_primitiveCharacter_le`, `NTKB.Davenport.sum_inv_totient_mul_le`, `NTKB.Davenport.sum_inv_totient_le`, `NTKB.Davenport.totient_mul_totient_le` | proved |  |
| 29-8 | 181 | Dyadic ranges: for U<q<=2U, B gives a bound O((x^2/U + U x)(log x)(log(Q/U))), and summing over U = Q 2^(-k) gives O(x^2 Q_1^(-1) (log x)^c + Q x log x) with Q_1 = (log x)^(A+c) | `NTKB.Davenport.sum_dyadic_le` | proved |  |
| 29-9 | 181 | Small moduli: for q<=Q_1 = (log x)^(A+c) and primitive chi, psi'(x,chi) << x exp(-c sqrt(log x)) by estimate (C) of section 22, so q<=Q_1 contribute O(x^2 (log x)^(-A) ) which is O(Q x log x); this completes the proof of (1) | `NTKB.Davenport.SiegelWalfiszHypothesis.primitive_bound` | proved, conditional |  |
