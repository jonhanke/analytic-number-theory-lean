# T. M. Apostol, *Introduction to Analytic Number Theory* (1976): map to the Lean library

Each row is a result of the book, the Lean declarations that formalize it, and its status, computed from the Lean kernel (an audit of the axioms and hypotheses of every declaration): *proved* means proved with only the standard axioms and no unproved input; *proved in part* that a part, a special case or one instance is proved; *proved, conditional* that an unproved input (a named statement) is assumed; *refuted as stated in the book* that the library proves the printed statement false and proves a corrected form (see the errata in the README); *in Mathlib* that Mathlib (a dependency) has the result and the Lean name is Mathlib's. Results that are only in Tau Ceti or PrimeNumberTheoremAnd (which this library does not depend on) are marked so. The statements in the third column are short descriptions, not quotations; read the book for the exact wording. The column *Also in* credits other libraries: Mathlib, Tau Ceti or PrimeNumberTheoremAnd declarations that prove the result, a part of it, or a closely related statement (as recorded by the coverage audit). Items are numbered as in the book (Theorem N.M, Lemma, Example); rows named *Definition* are definitions that the library or Mathlib formalizes. Pages are pages of the pdf file of the book (approximate for a few pages).

Rows: 322. proved: 168; in Mathlib: 148; in Tau Ceti only (not a dependency): 3; proved in part: 2; in PrimeNumberTheoremAnd only (not a dependency): 1. Proved here and also in another library: 81.


## Chapter 1

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 1.1 | 24 | Basic divisibility laws: reflexive, transitive, linear, multiplication, cancellation, 1 divides all, all divide 0 | `dvd_refl`, `dvd_trans`, `dvd_add`, `mul_dvd_mul_iff_left` | in Mathlib |  |
| Theorem 1.2 | 24 | Any a,b have a common divisor of the form ax+by | `Int.gcd_eq_gcd_ab`, `Nat.gcd_eq_gcd_ab`, `EuclideanDomain.gcd_eq_gcd_ab` | in Mathlib |  |
| Theorem 1.3 | 25 | Unique d>=0 that is a common divisor and divisible by every common divisor (the gcd) | `dvd_gcd_iff`, `gcd_eq_zero_iff` | in Mathlib |  |
| Theorem 1.4 | 26 | gcd is commutative, associative, (ac,bc)=abs(c)(a,b) | `gcd_comm`, `gcd_assoc`, `gcd_mul_right` | in Mathlib |  |
| Theorem 1.5 | 26 | Euclid's lemma: a divides bc and (a,b)=1 imply a divides c | `IsCoprime.dvd_of_dvd_mul_left` | in Mathlib |  |
| Theorem 1.6 | 26 | Every n>1 is prime or a product of primes | `Nat.prod_primeFactorsList` | in Mathlib |  |
| Theorem 1.7 | 26 | Infinitely many primes (Euclid) | `Nat.exists_infinite_primes` | in Mathlib |  |
| Theorem 1.8 | 27 | If prime p does not divide a then (p,a)=1 | `NTKB.Apostol.coprime_of_prime_not_dvd` | proved | Mathlib: `Nat.Prime.eq_one_or_self_of_dvd` |
| Theorem 1.9 | 27 | Prime dividing a product divides a factor; also for n factors | `Nat.Prime.dvd_mul`, `Prime.dvd_prod_iff`, `exists_mem_multiset_dvd` | in Mathlib |  |
| Theorem 1.10 | 28 | Fundamental theorem of arithmetic: unique prime-power factorization | `Nat.factorization_prod_pow_eq_self`, `Nat.eq_of_factorization_eq` | in Mathlib |  |
| Theorem 1.11 | 28 | Positive divisors of prod p_i^a_i are exactly prod p_i^c_i with 0<=c_i<=a_i | `Nat.factorization_le_iff_dvd`, `Nat.dvd_prime_pow` | in Mathlib |  |
| Theorem 1.12 | 28 | gcd of two numbers has exponents the minima | `Nat.factorization_gcd` | in Mathlib |  |
| Theorem 1.13 | 28 | Sum of 1/p diverges | `not_summable_one_div_on_primes` | in Mathlib |  |
| Theorem 1.14 | 29 | Division algorithm: unique q,r with a=bq+r, 0<=r<b; r=0 iff b divides a | `NTKB.Apostol.division_algorithm` | proved | Mathlib: `Int.ediv_emod_unique''` |
| Theorem 1.15 | 30 | Euclidean algorithm: last nonzero remainder is the gcd | `NTKB.Apostol.euclid_terminates`, `NTKB.Apostol.euclidPair` | proved | Mathlib: `Nat.xgcdAux_fst`, Mathlib: `EuclideanDomain.xgcdAux_fst` |
| Definition: prime, composite (D001, D011, D012) | 26 | Prime means n>1 with only divisors 1 and n | `Nat.Prime`, `Nat.prime_def` | in Mathlib |  |
| Definition: gcd, relatively prime (D008-D010, D016) | 25 | gcd and coprimality | `Nat.gcd_eq_gcd_ab`, `IsCoprime.dvd_of_dvd_mul_left` | in Mathlib |  |
| Definition: squarefree (D019) | 31 | Not divisible by the square of any prime | `Squarefree.ne_zero` | in Mathlib |  |
| Definition: Fermat numbers (D003) | 17 | F_n=2^(2^n)+1 | `Nat.fermatNumber`, `Nat.coprime_fermatNumber_fermatNumber` | in Mathlib |  |
| Definition: Pythagorean triple (D002) | 12 | (x,y,z) with x^2+y^2=z^2 | `PythagoreanTriple` | in Mathlib |  |

## Chapter 2

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 2.1 | 35 | Sum of mu(d) over d \\| n is [1/n] (1 if n=1, else 0) | `ArithmeticFunction.moebius_mul_coe_zeta`, `ArithmeticFunction.coe_zeta_mul_moebius` | in Mathlib |  |
| Theorem 2.2 | 36 | Sum of phi(d) over d \\| n equals n | `Nat.sum_totient` | in Mathlib |  |
| Theorem 2.3 | 36 | phi(n)=sum_{d \\| n} mu(d) n/d | `NTKB.Apostol.totient_eq_sum_moebius_mul` | proved | Mathlib: `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`, Mathlib: `Nat.sum_totient` |
| Theorem 2.4 | 37 | phi(n)=n prod_{p \\| n}(1-1/p) | `Nat.totient_eq_div_primeFactors_mul`, `Nat.totient_eq_prod_factorization` | in Mathlib |  |
| Theorem 2.5 | 38 | phi(p^a)=p^a-p^(a-1); phi(mn) formula with d=(m,n); multiplicative; a \\| b implies phi(a) \\| phi(b); phi(n) even for n>2 and 2^r divides phi(n) | `NTKB.Apostol.two_pow_card_odd_primeFactors_dvd_totient` | proved | Mathlib: `Nat.totient_prime_pow`, Mathlib: `Nat.totient_gcd_mul_totient_mul`, Mathlib: `Nat.totient_mul`, Mathlib: `Nat.totient_dvd_of_dvd`, Mathlib: `Nat.totient_even` |
| Theorem 2.6 | 39 | Dirichlet product is commutative and associative | — | in Mathlib |  |
| Theorem 2.7 | 40 | I*f=f*I=f (I=[1/n]) | `ArithmeticFunction.one_smul'` | in Mathlib |  |
| Theorem 2.8 | 40 | f with f(1)!=0 has a unique Dirichlet inverse, given recursively | `ArithmeticFunction.dirichletInverse`, `ArithmeticFunction.self_mul_dirichletInverse`, `ArithmeticFunction.dirichletInverse_mul_self`, `ArithmeticFunction.isUnit_iff_isUnit_apply_one` | in Mathlib |  |
| Theorem 2.9 | 42 | Mobius inversion: f(n)=sum_{d \\| n} g(d) iff g(n)=sum mu(d) f(n/d) | `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`, `ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq` | in Mathlib |  |
| Theorem 2.10 | 42 | log n = sum_{d \\| n} Lambda(d) | `ArithmeticFunction.vonMangoldt_sum` | in Mathlib |  |
| Theorem 2.11 | 43 | Lambda(n)= sum mu(d) log(n/d) = -sum mu(d) log d | `ArithmeticFunction.sum_moebius_mul_log_eq`, `ArithmeticFunction.moebius_mul_log_eq_vonMangoldt` | in Mathlib |  |
| Example 1 | 43 | f_alpha(n)=n^alpha is completely multiplicative | `NTKB.Apostol.isCompletelyMultiplicative_powC` | proved | PNT+: `ArithmeticFunction.powR`, PNT+: `ArithmeticFunction.isMultiplicative_powR`, PNT+: `CompletelyMultiplicative.zeta`, PNT+: `CompletelyMultiplicative.id` |
| Example 2 | 44 | Identity function I(n)=[1/n] is completely multiplicative | `NTKB.Apostol.isCompletelyMultiplicative_one` | proved | Mathlib: `ArithmeticFunction.isMultiplicative_one` |
| Example 3 | 44 | mu is multiplicative but not completely multiplicative | `NTKB.Apostol.not_isCompletelyMultiplicative_moebius` | proved | Mathlib: `ArithmeticFunction.isMultiplicative_moebius` |
| Example 4 | 44 | phi is multiplicative, not completely (phi(4)=2, phi(2)^2=1) | `NTKB.Apostol.totient_four_ne` | proved | Mathlib: `Nat.totient_mul` |
| Theorem 2.12 | 44 | A multiplicative f has f(1)=1 | `ArithmeticFunction.IsMultiplicative.map_one` | in Mathlib |  |
| Theorem 2.13 | 44 | With f(1)=1: f multiplicative iff f(prod p^a)=prod f(p^a); completely multiplicative iff f(p^a)=f(p)^a | `NTKB.Apostol.isMultiplicative_iff_factorization`, `NTKB.Apostol.isCompletelyMultiplicative_iff_prime_pow` | proved | Mathlib: `ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers`, Mathlib: `ArithmeticFunction.IsMultiplicative.iff_ne_zero`, PNT+: `CompletelyMultiplicative.apply_pow`, PNT+: `CompletelyMultiplicative.isMultiplicative` |
| Theorem 2.14 | 45 | Dirichlet product of multiplicative functions is multiplicative | `ArithmeticFunction.IsMultiplicative.mul` | in Mathlib |  |
| Theorem 2.15 | 45 | If g and f*g are multiplicative then f is multiplicative | `NTKB.Apostol.isMultiplicative_of_isMultiplicative_mul` | proved |  |
| Theorem 2.16 | 46 | Dirichlet inverse of multiplicative g is multiplicative | `NTKB.Apostol.isMultiplicative_of_mul_eq_one`, `NTKB.Apostol.isMultiplicative_dirichletInverse` | proved |  |
| Theorem 2.17 | 46 | Multiplicative f is completely multiplicative iff f^{-1}=mu*f | `NTKB.Apostol.isCompletelyMultiplicative_iff_pmul_moebius_mul_eq_one` | proved |  |
| Theorem 2.18 | 47 | Multiplicative f: sum_{d \\| n} mu(d) f(d)=prod_{p \\| n}(1-f(p)) | `ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub` | in Mathlib |  |
| Theorem 2.19 | 48 | sum_{d \\| n} lambda(d)=1 if n square else 0; lambda^{-1}=abs(mu) | `NTKB.Apostol.sum_divisors_liouville`, `NTKB.Apostol.pmul_moebius_moebius_mul_liouville`, `NTKB.Apostol.pmul_moebius_moebius_apply` | proved |  |
| Theorem 2.20 | 49 | Inverse of sigma_alpha is sum_{d \\| n} d^alpha mu(d) mu(n/d) | `NTKB.Apostol.sigmaC_mul_inv`, `NTKB.Apostol.pmul_moebius_powC_mul_moebius_apply`, `NTKB.Apostol.sigmaC`, `NTKB.Apostol.powC`, `NTKB.Apostol.sigmaC_natCast` | proved |  |
| Theorem 2.21 | 49 | alpha o (beta o F) = (alpha*beta) o F (generalized convolution) | `NTKB.Apostol.genConv_genConv`, `NTKB.Apostol.genConv` | proved |  |
| Theorem 2.22 | 50 | Generalized inversion: G=alpha o F iff F=alpha^{-1} o G | `NTKB.Apostol.genConv_inversion` | proved |  |
| Theorem 2.23 | 50 | Generalized Mobius inversion for completely multiplicative alpha | `NTKB.Apostol.genConv_moebius_inversion` | proved |  |
| Theorem 2.24 | 53 | Multiplicative f=g iff Bell series agree for all primes | `NTKB.Apostol.eq_iff_bellSeries_eq`, `NTKB.Apostol.bellSeries` | proved | Mathlib: `ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers` |
| Theorem 2.25 | 54 | Bell series of f*g mod p is the product of Bell series | `NTKB.Apostol.bellSeries_mul`, `NTKB.Apostol.bellSeries_moebius`, `NTKB.Apostol.bellSeries_mul_one_sub_of_isCompletelyMultiplicative` | proved |  |
| Theorem 2.26 | 55 | Derivative f'(n)=f(n)log n: sum, Leibniz, inverse rules | `NTKB.Apostol.arithDeriv_add`, `NTKB.Apostol.arithDeriv_mul`, `NTKB.Apostol.arithDeriv_inv` | proved |  |
| Theorem 2.27 | 56 | Selberg identity: Lambda(n)log n + sum Lambda(d)Lambda(n/d) = sum mu(d)log^2(n/d) | `NTKB.Apostol.selberg_identity`, `NTKB.Apostol.arithDeriv_vonMangoldt_add_mul_self` | proved |  |
| Definition: arithmetical function, Dirichlet product (D020, D021, D026) | 34 | Complex-valued functions on positive integers with convolution | `ArithmeticFunction` | in Mathlib |  |
| Definition: Mobius function (no candidate id) | 34 | mu(n)=1, (-1)^k for k distinct primes, 0 otherwise | `ArithmeticFunction.moebius` | in Mathlib |  |
| Definition: Euler totient (D022-D025) | 35 | phi(n) counts 1<=k<=n coprime to n | `Nat.totient` | in Mathlib |  |
| Definition: identity and unit functions (D027) | 40 | I(n)=[1/n], u(n)=1 | `ArithmeticFunction.zeta` | in Mathlib |  |
| Definition: Mangoldt function (D028) | 42 | Lambda(n)=log p if n=p^m else 0 | `ArithmeticFunction.vonMangoldt` | in Mathlib |  |
| Definition: multiplicative, completely multiplicative (D029, D030) | 43 | Multiplicativity on coprime arguments | `ArithmeticFunction.IsMultiplicative`, `CompletelyMultiplicative`, `ArithmeticFunction.IsCompletelyMultiplicative`, `NTKB.Apostol.IsCompletelyMultiplicative` | in Mathlib |  |
| Definition: Liouville function (D033) | 47 | lambda(1)=1, lambda(n)=(-1)^(sum a_i) | `ArithmeticFunction.liouville` | in Mathlib |  |
| Definition: divisor functions (D034, D035) | 48 | sigma_alpha(n)=sum d^alpha | `ArithmeticFunction.sigma`, `ArithmeticFunction.sigmaR`, `NTKB.Apostol.sigmaC`, `NTKB.Apostol.powC` | in Mathlib |  |
| Definition: formal power series, Cauchy product, inverse (D036-D042) | 51 | Formal power series ring and invertibility when a(0)!=0 | `PowerSeries.coeff_mul` | in Mathlib |  |
| Definition: derivative of arithmetical function (D043) | 55 | f'(n)=f(n)log n | `NTKB.Apostol.arithDeriv` | proved |  |
| Definition: Mobius function of order k (D044) | 60 | mu_k(n) | `NTKB.Apostol.moebiusOrder`, `NTKB.Apostol.moebiusOrder_one` | proved |  |

## Chapter 3

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 3.1 | 64 | Euler summation: $\sum_{y<n\le x} f(n)=\int_y^x f+\int_y^x (t-\lfloor t\rfloor) f'(t)dt+f(x)(\lfloor x\rfloor-x)-f(y)(\lfloor y\rfloor-y)$ for $C^1$ $f$ | `NTKB.Apostol.euler_summation` | proved | PNT+: `sum_eq_integral_add_integral_deriv` |
| Theorem 3.2 | 65 | For $x\ge1$: $\sum_{n\le x}1/n=\log x+C+O(1/x)$; $\sum n^{-s}=x^{1-s}/(1-s)+\zeta(s)+O(x^{-s})$; tail $=O(x^{1-s})$ for $s>1$; $\sum n^\alpha=x^{\alpha+1}/(\alpha+1)+O(x^\alpha)$ | `NTKB.Apostol.abs_sum_inv_sub_log_sub_eulerMascheroni_le`, `NTKB.Apostol.apostol_thm_3_2_b`, `NTKB.Apostol.exists_abs_sum_inv_sqrt_sub_le`, `NTKB.Apostol.abs_tsum_rpow_neg_sub_le`, `NTKB.Apostol.abs_tsum_sub_sum_Ioc_le`, `NTKB.Apostol.abs_sum_rpow_sub_le`, `NTKB.Apostol.abs_floor_sub_le`, `NTKB.Apostol.abs_sum_id_sub_sq_div_two_le` | proved | PNT+: `ZetaSum_aux2`, PNT+: `ZetaBnd_aux1b` |
| Theorem 3.3 | 67 | $\sum_{n\le x} d(n)=x\log x+(2C-1)x+O(\sqrt x)$ | `NTKB.Apostol.abs_sum_sigma_zero_sub_le` | proved |  |
| Theorem 3.4 | 70 | $\sum_{n\le x}\sigma_1(n)=\frac{\pi^2}{12}x^2+O(x\log x)$ | `NTKB.Apostol.abs_sum_sigma_one_sub_le` | proved |  |
| Theorem 3.5 | 70 | For $\alpha>0,\alpha\ne1$: $\sum_{n\le x}\sigma_\alpha(n)=\frac{\zeta(\alpha+1)}{\alpha+1}x^{\alpha+1}+O(x^\beta)$, $\beta=\max(1,\alpha)$ | `NTKB.Apostol.exists_abs_sum_sigma_rpow_sub_le` | proved |  |
| Theorem 3.6 | 71 | $\sum_{n\le x}\sigma_{-\beta}(n)=\zeta(\beta+1)x+O(x^\delta)$ ($\beta\ne1$), $=\zeta(2)x+O(\log x)$ for $\beta=1$ | `NTKB.Apostol.exists_abs_sum_sigma_rpow_neg_sub_le`, `NTKB.Apostol.abs_sum_sigma_neg_one_sub_le` | proved |  |
| Theorem 3.7 | 72 | $\sum_{n\le x}\varphi(n)=\frac{3}{\pi^2}x^2+O(x\log x)$ | `NTKB.Apostol.abs_sum_totient_sub_le`, `NTKB.Apostol.hasSum_moebius_div_sq` | proved |  |
| Theorem 3.8 | 72 | Lattice points $(a,b),(m,n)$ are mutually visible iff $\gcd(a-m,b-n)=1$ | `NTKB.Apostol.mutuallyVisible_iff_gcd_eq_one`, `NTKB.Apostol.MutuallyVisible` | proved |  |
| Theorem 3.9 | 73 | The set of lattice points visible from the origin has density $6/\pi^2$ | `NTKB.Apostol.tendsto_visibleCount_div_latticeCount`, `NTKB.Apostol.visibleCount`, `NTKB.Apostol.latticeCount`, `NTKB.Apostol.card_gcd_eq_one_latticeSquare` | proved |  |
| Theorem 3.10 | 75 | If $h=f*g$ with partial sums $F,G,H$ then $H(x)=\sum_{n\le x}f(n)G(x/n)=\sum_{n\le x}g(n)F(x/n)$ | `ArithmeticFunction.sum_Ioc_mul_eq_sum_sum`, `ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter` | in Mathlib |  |
| Theorem 3.11 | 75 | $\sum_{n\le x}\sum_{d\mid n}f(d)=\sum_{n\le x}f(n)\lfloor x/n\rfloor=\sum_{n\le x}F(x/n)$ | `ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum`, `NTKB.Apostol.sum_mul_div_eq_sum_sum` | in Mathlib |  |
| Theorem 3.12 | 76 | $\sum_{n\le x}\mu(n)\lfloor x/n\rfloor=1$ and $\sum_{n\le x}\Lambda(n)\lfloor x/n\rfloor=\log\lfloor x\rfloor!$ | `NTKB.Apostol.sum_moebius_mul_floor`, `NTKB.Apostol.sum_vonMangoldt_mul_floor` | proved | PNT+: `sum_mobius_floor`, PNT+: `Mertens.sum_log_eq_sum_mangoldt`, PNT+: `Mertens.sum_log_eq_log_factorial` |
| Theorem 3.13 | 76 | $\left \\| \sum_{n\le x}\mu(n)/n\right \\| \le1$ for $x\ge1$ | `NTKB.Apostol.abs_sum_moebius_div_le` | proved | PNT+: `sum_mobius_div_self_le` |
| Theorem 3.14 | 77 | Legendre: $\lfloor x\rfloor!=\prod_{p\le x}p^{\alpha(p)}$ with $\alpha(p)=\sum_{m\ge1}\lfloor x/p^m\rfloor$ | `NTKB.Apostol.factorial_floor_eq_prod` | proved | Mathlib: `Nat.Prime.emultiplicity_factorial` |
| Theorem 3.15 | 77 | $\log\lfloor x\rfloor!=x\log x-x+O(\log x)$, hence $\sum_{n\le x}\Lambda(n)\lfloor x/n\rfloor=x\log x-x+O(\log x)$ | `Real.sum_log_le`, `Real.le_sum_log`, `Real.sum_log_eq_log_factorial` | in Mathlib |  |
| Theorem 3.16 | 78 | $\sum_{p\le x}\lfloor x/p\rfloor\log p=x\log x+O(x)$ | `NTKB.Apostol.exists_abs_sum_prime_floor_mul_log_sub_le` | proved |  |
| Theorem 3.17 | 79 | Hyperbola identity $\sum_{qd\le x}f(d)g(q)=\sum_{n\le a}f(n)G(x/n)+\sum_{n\le b}g(n)F(x/n)-F(a)G(b)$ for $ab=x$ | `NTKB.Apostol.sum_mul_eq_hyperbola`, `NTKB.Apostol.sum_Ioc_sum_divisorsAntidiagonal` | proved |  |
| Definition: big oh | 63 | $f=O(g)$ iff $f/g$ bounded for $x>a$ | `Asymptotics.IsBigO` | in Mathlib |  |
| Definition: asymptotic equality | 63 | $f\sim g$ iff $f/g\to1$ | `Asymptotics.IsEquivalent` | in Mathlib |  |
| Definition: Riemann zeta | 65 | $\zeta(s)=\sum n^{-s}$ for $s>1$, continued to $0<s<1$ | `zeta_eq_tsum_one_div_nat_cpow` | in Mathlib |  |
| Definition: fractional part | 82 | $\{x\}=x-\lfloor x\rfloor$ | `Int.fract` | in Mathlib |  |

## Chapter 4

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 4.1 | 86 | $0\le\psi(x)/x-\vartheta(x)/x\le(\log x)^2/(2\sqrt x\log2)$; hence $\psi/x\to1$ iff $\vartheta/x\to1$ | `NTKB.Apostol.apostol_thm_4_1` | proved | Mathlib: `Chebyshev.theta_le_psi`, Mathlib: `Chebyshev.psi_sub_theta_le`, Mathlib: `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`, Mathlib: `Chebyshev.isBigO_psi_sub_theta_sqrt`, PNT+: `chebyshev_asymptotic` |
| Theorem 4.2 | 87 | Abel's identity: $\sum_{y<n\le x}a(n)f(n)=A(x)f(x)-A(y)f(y)-\int_y^xA(t)f'(t)dt$ | `sum_mul_eq_sub_sub_integral_mul`, `sum_mul_eq_sub_integral_mul` | in Mathlib |  |
| Theorem 4.3 | 88 | $\vartheta(x)=\pi(x)\log x-\int_2^x\pi(t)/t\,dt$ and $\pi(x)=\vartheta(x)/\log x+\int_2^x\vartheta(t)/(t\log^2t)dt$ | `Chebyshev.theta_eq_primeCounting_mul_log_sub_integral`, `Chebyshev.primeCounting_eq_theta_div_log_add_integral` | in Mathlib |  |
| Theorem 4.4 | 89 | Equivalent forms of PNT: $\pi(x)\log x/x\to1$; $\vartheta(x)/x\to1$; $\psi(x)/x\to1$ | `NTKB.Apostol.apostol_thm_4_4` | proved | Mathlib: `Chebyshev.primeCounting_sub_theta_div_log_isBigO`, Mathlib: `Chebyshev.integral_theta_div_log_sq_isLittleO`, PNT+: `chebyshev_asymptotic`, PNT+: `WeakPNT''`, PNT+: `pi_alt'` |
| Theorem 4.5 | 90 | Equivalent: $\pi(x)\log x/x\to1$; $\pi(x)\log\pi(x)/x\to1$; $p_n/(n\log n)\to1$ | `NTKB.Apostol.apostol_thm_4_5`, `NTKB.Apostol.piR` | proved | PNT+: `pi_alt'`, PNT+: `nth_prime_asymp`, PNT+: `pn_asymptotic`, PNT+: `pi_nth_prime_asymp` |
| Theorem 4.6 | 92 | For $n\ge2$: $\frac16\frac n{\log n}<\pi(n)<6\frac n{\log n}$ | `NTKB.Apostol.primeCounting_gt`, `NTKB.Apostol.primeCounting_lt` | proved | Mathlib: `Chebyshev.pi_ge_of_four_le`, Mathlib: `Chebyshev.pi_ge`, Mathlib: `Chebyshev.pi_le_log4_mul_div`, Mathlib: `Chebyshev.eventually_primeCounting_le` |
| Theorem 4.7 | 94 | $\frac16 n\log n<p_n<12(n\log n+n\log\frac{12}e)$ for $n\ge1$ | `NTKB.Apostol.nth_prime_bounds` | proved | PNT+: `Rosser1938.p_n_gt_1` |
| Theorem 4.8 | 95 | Shapiro: $a(n)\ge0$, $\sum a(n)\lfloor x/n\rfloor=x\log x+O(x)$ implies $\sum a(n)/n$ form, $\sum_{n\le x}a(n)=O(x)$, and $\ge Ax$ for large $x$ | `NTKB.Apostol.shapiro` | proved |  |
| Theorem 4.9 | 98 | $\sum_{n\le x}\Lambda(n)/n=\log x+O(1)$; $c_2x<\psi(x)<c_1x$ | `NTKB.Apostol.apostol_thm_4_9` | proved | PNT+: `Mertens.sum_mangoldt_div_eq_log`, PNT+: `Mertens.E₁Λ.bounded`, Mathlib: `Chebyshev.psi_le_const_mul_self`, Mathlib: `Chebyshev.psi_ge'`, Mathlib: `Chebyshev.psi_ge_of_seven_le` |
| Theorem 4.10 | 99 | $\sum_{p\le x}\log p/p=\log x+O(1)$; $c_2x<\vartheta(x)<c_1x$ | `NTKB.Apostol.apostol_thm_4_10` | proved | PNT+: `Mertens.sum_log_prime_div_eq_log`, PNT+: `Mertens.E₁p.bounded`, Mathlib: `Chebyshev.theta_le_log4_mul_x`, Mathlib: `Chebyshev.theta_ge'` |
| Theorem 4.11 | 99 | $\sum_{n\le x}\psi(x/n)=x\log x-x+O(\log x)$ and $\sum_{n\le x}\vartheta(x/n)=x\log x+O(x)$ | `NTKB.Apostol.abs_sum_psi_div_sub_le`, `NTKB.Apostol.exists_abs_sum_theta_div_sub_le` | proved | PNT+: `Mertens.sum_log_eq_sum_mangoldt`, Mathlib: `Real.sum_log_le`, Mathlib: `Real.le_sum_log` |
| Theorem 4.12 | 100 | $\sum_{p\le x}1/p=\log\log x+A+O(1/\log x)$ for $x\ge2$ | `NTKB.Apostol.apostol_thm_4_12` | proved | PNT+: `Mertens.sum_prime_div_eq_log_log`, PNT+: `Mertens.E₂p.bound`, PNT+: `Mertens.sum_prime_div_eq`, PNT+: `mertens_second_theorem` |
| Theorem 4.13 | 101 | $M(x)/x\to0$ iff $H(x)/(x\log x)\to0$ where $H=\sum\mu(n)\log n$ | `NTKB.Apostol.tendsto_mertens_div_iff` | proved |  |
| Theorem 4.14 | 102 | PNT implies $H(x)/(x\log x)\to0$ (hence $M(x)=o(x)$) | `NTKB.Apostol.tendsto_mertensLog_div_of_psi`, `NTKB.Apostol.tendsto_mertens_div_of_psi`, `NTKB.Apostol.sum_moebius_mul_psi_div` | proved | PNT+: `mu_pnt`, PNT+: `M_isLittleO`, PNT+: `sum_mu_Lambda` |
| Theorem 4.15 | 104 | $M(x)=o(x)$ implies $\psi(x)\sim x$ | `NTKB.Apostol.tendsto_psi_div_of_mertens` | proved |  |
| Theorem 4.16 | 107 | $\sum_{n\le x}\mu(n)/n=o(1)$ implies PNT | `NTKB.Apostol.tendsto_psi_div_of_sum_moebius_div` | proved |  |
| Theorem 4.17 | 109 | For $F$ on $(0,\infty)$ and $G(x)=\log x\sum_{n\le x}F(x/n)$, an identity expressing $F(x)\log x+\sum_{n\le x}F(x/n)\Lambda(n)$ as a Mobius-weighted sum $\sum_{d\le x}\mu(d)G(x/d)$ (Selberg-type inversion) | `NTKB.Apostol.tatuzawa_iseki` | proved in part |  |
| Theorem 4.18 | 110 | Selberg: $\psi(x)\log x+\sum_{n\le x}\Lambda(n)\psi(x/n)=2x\log x+O(x)$ | `NTKB.Apostol.selberg_asymptotic_formula` | proved |  |
| Definition: Chebyshev $\psi$ | 85 | $\psi(x)=\sum_{n\le x}\Lambda(n)$ | `Chebyshev.psi` | in Mathlib |  |
| Definition: Chebyshev $\vartheta$ | 85 | $\vartheta(x)=\sum_{p\le x}\log p$ | `Chebyshev.theta` | in Mathlib |  |
| Definition: $M(x)$ | 101 | $M(x)=\sum_{n\le x}\mu(n)$ | `NTKB.Apostol.mertens`, `NTKB.Apostol.mertensLog` | proved | PNT+: `M` |

## Chapter 5

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 5.1 | 117 | Congruence mod m is reflexive, symmetric and transitive | `Int.ModEq.refl`, `Int.ModEq.symm`, `Int.ModEq.trans` | in Mathlib |  |
| Theorem 5.2 | 117 | Congruences with equal modulus can be added, multiplied, raised to powers | `Int.ModEq.mul_left`, `Int.ModEq.mul_right`, `Int.ModEq.pow` | in Mathlib |  |
| Theorem 5.3 | 118 | For c>0, a=b (mod m) iff ac=bc (mod mc) | `Int.ModEq.mul_left_cancel_iff'` | in Mathlib |  |
| Theorem 5.4 | 119 | Cancellation: ac=bc (mod m) gives a=b (mod m/gcd(m,c)) | `Int.ModEq.cancel_left_div_gcd`, `Nat.ModEq.cancel_left_div_gcd` | in Mathlib |  |
| Theorem 5.5 | 119 | If a=b (mod m) and d divides both m and a then d divides b | `Int.ModEq.dvd_iff`, `Int.ModEq.of_dvd` | in Mathlib |  |
| Theorem 5.6 | 119 | If a=b (mod m) then gcd(a,m)=gcd(b,m) | `Nat.ModEq.gcd_eq` | in Mathlib |  |
| Theorem 5.7 | 119 | If a=b (mod m) and 0<abs(b-a)<m then a=b | `NTKB.Apostol.eq_of_modEq_of_abs_sub_lt` | proved |  |
| Theorem 5.8 | 119 | a=b (mod m) iff a and b leave the same remainder | `Int.ModEq`, `Nat.ModEq` | in Mathlib |  |
| Theorem 5.9 | 119 | a=b mod m and mod n with gcd(m,n)=1 gives a=b mod mn | `Int.modEq_and_modEq_iff_modEq_mul`, `Nat.modEq_and_modEq_iff_modEq_mul` | in Mathlib |  |
| Theorem 5.10 | 120 | Residue classes: a-bar = b-bar iff a=b mod m; the m classes 0..m-1 are disjoint and cover Z | `NTKB.Apostol.residueClass_eq_iff`, `NTKB.Apostol.isCompleteResidueSystem_range` | proved | Mathlib: `ZMod.chineseRemainder` |
| Theorem 5.11 | 120 | If gcd(k,m)=1, multiplying a complete residue system by k gives a complete residue system | `NTKB.Apostol.IsCompleteResidueSystem.mul` | proved | Mathlib: `Units.mulLeft_bijective` |
| Theorem 5.12 | 121 | If gcd(a,m)=1 then ax=b (mod m) has exactly one solution mod m | `NTKB.Apostol.existsUnique_mul_eq` | proved | Mathlib: `Nat.exists_mul_mod_eq_of_coprime` |
| Theorem 5.13 | 121 | With d=gcd(a,m), ax=b (mod m) is solvable iff d divides b | `NTKB.Apostol.exists_mul_modEq_iff` | proved | Mathlib: `Nat.exists_mul_mod_eq_gcd` |
| Theorem 5.14 | 122 | If d=gcd(a,m) divides b, ax=b (mod m) has exactly d solutions mod m, explicitly listed | `NTKB.Apostol.card_mul_eq` | proved |  |
| Theorem 5.15 | 123 | If gcd(a,b)=d, there are x,y with ax+by=d | `Int.gcd_eq_gcd_ab`, `Nat.gcd_eq_gcd_ab` | in Mathlib |  |
| Theorem 5.16 | 123 | If {a_i} is a reduced residue system mod m and gcd(k,m)=1 then {k a_i} is too | `NTKB.Apostol.IsReducedResidueSystem.mul` | proved | Mathlib: `Units.mulLeft_bijective`, Mathlib: `Group.mulLeft_bijective` |
| Theorem 5.17 | 123 | Euler-Fermat: gcd(a,m)=1 implies a^phi(m)=1 (mod m) | `Nat.ModEq.pow_totient`, `ZMod.pow_totient` | in Mathlib |  |
| Theorem 5.18 | 123 | If p does not divide a then a^(p-1)=1 (mod p) | `ZMod.pow_card_sub_one_eq_one`, `FiniteField.pow_card_sub_one_eq_one` | in Mathlib |  |
| Theorem 5.19 | 124 | Little Fermat: a^p=a (mod p) for every a and prime p | `ZMod.pow_card`, `FiniteField.pow_card` | in Mathlib |  |
| Theorem 5.20 | 124 | If gcd(a,m)=1 the solution of ax=b (mod m) is x = b a^(phi(m)-1) | `NTKB.Apostol.mul_pow_totient_sub_one` | proved | Mathlib: `Nat.ModEq.pow_totient` |
| Theorem 5.21 | 125 | Lagrange: a degree n polynomial with leading coefficient prime to p has at most n roots mod p | `NTKB.Apostol.card_solutions_le_natDegree` | proved | Mathlib: `Polynomial.card_roots'` |
| Theorem 5.22 | 125 | If f of degree n has more than n roots mod p, all coefficients are divisible by p | `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`, `Polynomial.eq_of_natDegree_lt_card_of_eval_eq` | in Mathlib |  |
| Theorem 5.23 | 126 | All coefficients of (x-1)...(x-p+1) - x^(p-1) + 1 are divisible by p | `NTKB.Apostol.dvd_coeff_prod_X_sub_sub` | proved |  |
| Theorem 5.24 | 126 | Wilson: (p-1)! = -1 (mod p) | `ZMod.wilsons_lemma` | in Mathlib |  |
| Theorem 5.25 | 126 | Wolstenholme: for prime p>5, the sum of 1/k for k<p is 0 mod p^2 (in the book's form) | `NTKB.Apostol.wolstenholme` | proved |  |
| Theorem 5.26 | 127 | Chinese remainder: pairwise coprime moduli give a system with a unique solution mod the product | `Nat.chineseRemainder`, `Nat.chineseRemainderOfFinset`, `ZMod.chineseRemainder` | in Mathlib |  |
| Theorem 5.27 | 128 | CRT with coefficients: a_k x = b_k (mod m_k), gcd(a_k,m_k)=1, has a unique solution mod m | `NTKB.Apostol.existsUnique_mul_cast_eq` | proved |  |
| Theorem 5.28 | 128 | f(x)=0 mod m1...mr has solutions equal to the product of the solution counts mod each m_i | `NTKB.Apostol.card_roots_prod_eq` | proved |  |
| Theorem 5.29 | 129 | Visible lattice points contain arbitrarily large square gaps | `NTKB.Apostol.exists_square_gap_not_visible` | proved |  |
| Theorem 5.30 | 131 | Hensel lifting of a solution of f(x)=0 mod p^(a-1) to mod p^a (simple root case and the derivative-zero case) | `NTKB.Apostol.dvd_eval_add_iff`, `NTKB.Apostol.existsUnique_lift`, `NTKB.Apostol.lift_of_dvd_derivative` | proved | Mathlib: `hensels_lemma` |
| Theorem 5.31 | 133 | Principle of cross-classification (inclusion-exclusion) for the count of elements outside all S_i | `Finset.inclusion_exclusion_card_inf_compl`, `Finset.inclusion_exclusion_card_biUnion` | in Mathlib |  |
| Theorem 5.32 | 134 | The set r+td (t=1..k/d) contains phi(k)/phi(d) elements prime to k | `NTKB.Apostol.card_coprime_add_mul` | proved |  |
| Theorem 5.33 | 135 | A reduced residue system mod k decomposes into phi(k)/phi(d) disjoint reduced residue systems mod d | `NTKB.Apostol.exists_partition_units`, `NTKB.Apostol.card_fiber_unitsMap` | proved |  |
| Definition (complete residue system) | 120 | m integers, one from each residue class, form a complete residue system | `NTKB.Apostol.IsCompleteResidueSystem`, `NTKB.Apostol.IsReducedResidueSystem` | proved |  |
| Definition (reciprocal mod m) | 121 | Unique solution of ax=1 (mod m) when gcd(a,m)=1 is the reciprocal of a | `NTKB.Apostol.reciprocalMod`, `NTKB.Apostol.mul_reciprocalMod` | proved |  |

## Chapter 6

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 6.1 | 140 | Cancellation laws in a group | `mul_right_cancel`, `mul_left_cancel` | in Mathlib |  |
| Theorem 6.2 | 140 | $e^{-1}=e$, $(a^{-1})^{-1}=a$, $(ab)^{-1}=b^{-1}a^{-1}$ | `inv_one`, `inv_inv`, `mul_inv_rev` | in Mathlib |  |
| Theorem 6.3 | 141 | Laws of integer powers: $a^ma^n=a^{m+n}$, $(a^m)^n=a^{mn}$ (and $(ab)^n=a^nb^n$ when commuting) | `zpow_add`, `zpow_mul` | in Mathlib |  |
| Theorem 6.4 | 141 | Subgroup criterion: nonempty subset closed under product and inverse is a subgroup | `NTKB.Apostol.subgroupOfClosed` | proved | Mathlib: `Subgroup.ofDiv` |
| Theorem 6.5 | 142 | In a finite group each element has a power $a^n=e$ with $1\le n\le \\| G \\| $ | `isOfFinOrder_of_finite`, `orderOf_pos_iff`, `orderOf_le_card_univ` | in Mathlib |  |
| Theorem 6.6 | 142 | Extending a proper subgroup $G'$ of a finite abelian group by an element $a\notin G'$ with indicator $h$ gives a subgroup $G''=\{xa^k\}$ of order $h \\| G' \\| $ | `NTKB.Apostol.extendSubgroup`, `NTKB.Apostol.le_extendSubgroup_and_card`, `NTKB.Apostol.indicator` | proved |  |
| Theorem 6.7 | 143 | A character $f$ of a finite group has $f(e)=1$ and values are roots of unity | `MulChar.map_one`, `MulChar.pow_card_eq_one` | in Mathlib |  |
| Theorem 6.8 | 144 | A finite abelian group of order $n$ has exactly $n$ characters | `AddChar.card_eq`, `MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity` | in Mathlib |  |
| Theorem 6.9 | 145 | Characters of $G$ form an abelian group of order $n$ under pointwise product, identity the principal character | `MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity` | in Mathlib |  |
| Theorem 6.10 | 146 | Row sums of the character table: $n$ for the principal character, $0$ otherwise | `MulChar.sum_eq_zero_of_ne_one`, `AddChar.sum_eq_ite` | in Mathlib |  |
| Theorem 6.11 | 146 | Character table matrix $A$ satisfies $AA^*=nI$ | `NTKB.Apostol.charMatrix_mul_conjTranspose`, `NTKB.Apostol.charMatrix` | proved | Mathlib: `AddChar.sum_apply_eq_ite`, Mathlib: `DirichletCharacter.sum_char_inv_mul_char_eq` |
| Theorem 6.12 | 147 | Orthogonality relations for characters (sum over characters of $f(a)\overline{f(b)}$) | `DirichletCharacter.sum_char_inv_mul_char_eq`, `AddChar.sum_apply_eq_ite` | in Mathlib |  |
| Theorem 6.13 | 147 | Column sums of the table: $n$ if $a=e$, $0$ otherwise | `AddChar.sum_apply_eq_ite`, `DirichletCharacter.sum_characters_eq` | in Mathlib |  |
| Theorem 6.14 | 148 | Reduced residue classes mod $k$ form an abelian group of order $\varphi(k)$ | `ZMod.card_units_eq_totient` | in Mathlib |  |
| Theorem 6.15 | 148 | There are $\varphi(k)$ Dirichlet characters mod $k$, completely multiplicative, periodic mod $k$ | `DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity` | in Mathlib |  |
| Theorem 6.16 | 150 | $\sum_{\chi}\chi(m)\overline{\chi(n)}=\varphi(k)$ if $m\equiv n$ else $0$, for $(n,k)=1$ | `DirichletCharacter.sum_char_inv_mul_char_eq` | in Mathlib |  |
| Theorem 6.17 | 150 | For nonprincipal $\chi$ and monotone $f$ with continuous derivative, $\sum_{x<n\le y}\chi(n)f(n)=O(f(x))$ | `NTKB.Apostol.norm_sum_Ioc_floor_char_mul_le`, `NTKB.Apostol.tendsto_sum_char_mul_and_norm_sub_le` | proved | Tau Ceti: `norm_sum_Icc_le_level`, Mathlib: `DirichletCharacter.norm_le_one` |
| Theorem 6.18 | 151 | For nonprincipal $\chi$: $\sum_{n\le x}\chi(n)/n=L(1,\chi)+O(1/x)$ | `NTKB.Apostol.norm_sum_char_div_sub_LOne_le`, `NTKB.Apostol.norm_sum_char_log_div_add_LOneDeriv_le`, `NTKB.Apostol.norm_sum_char_div_sqrt_sub_LHalf_le` | proved |  |
| Theorem 6.19 | 152 | For real $\chi$, $A(n)=\sum_{d\mid n}\chi(d)\ge0$ and $\ge1$ when $n$ is a square | `NTKB.Apostol.sum_divisors_char_nonneg` | proved |  |
| Theorem 6.20 | 152 | For real nonprincipal $\chi$, $L(1,\chi)\ne0$ (via $B(x)\to\infty$ and $B(x)=2^cL(1,\chi)+O(1)$) | `NTKB.Apostol.tendsto_realCharB`, `NTKB.Apostol.exists_norm_realCharB_sub_le`, `NTKB.Apostol.LOne_ne_zero_of_isQuadratic` | proved | Mathlib: `DirichletCharacter.LFunction_apply_one_ne_zero` |
| Definitions: abelian group, finite group and order, subgroup, cyclic subgroup, nth roots of unity group | 139-141 | Group-theoretic vocabulary (D074-D080) | `CommGroup`, `Subgroup`, `Subgroup.zpowers` | in Mathlib |  |
| Definition: character of a group, principal character, Dirichlet character, periodic function | 143-155 | Character $f$ of $G$ (D081-D084, D087, D088, D090, D091) | `MulChar`, `DirichletCharacter` | in Mathlib |  |
| Definition: $L(1,\chi)$ | 158 | $L(1,\chi)=\sum_{n\ge1}\chi(n)/n$ for $\chi\ne\chi_1$ | `NTKB.Apostol.LOne`, `NTKB.Apostol.LOneDeriv`, `NTKB.Apostol.LHalf`, `NTKB.Apostol.seriesSum` | proved | Mathlib: `DirichletCharacter.LFunction` |

## Chapter 7

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 7.1 | 157 | Infinitely many primes $\equiv 3\pmod 4$ | `Nat.forall_exists_prime_gt_and_modEq` | in Mathlib |  |
| Theorem 7.2 | 157 | Infinitely many primes $\equiv 1\pmod 4$ | `Nat.infinite_setOfPred_prime_modEq_one` | in Mathlib |  |
| Theorem 7.3 | 158 | For $(h,k)=1$: $\sum_{p\le x,\,p\equiv h}\frac{\log p}{p}=\frac{1}{\varphi(k)}\log x+O(1)$ | `NTKB.Apostol.dirichlet_sum_log_div_prime`, `NTKB.Apostol.LOne_ne_zero`, `NTKB.Apostol.numLOneZero_eq_zero` | proved |  |
| Lemma 7.4 | 159 | Reduction of 7.3 to a character sum over primes (via orthogonality) | `NTKB.Apostol.lemma_7_4` | proved |  |
| Lemma 7.5 | 159 | For $\chi\ne\chi_1$: $\sum_{p\le x}\chi(p)\log p/p=O(1)$ | `NTKB.Apostol.lemma_7_5` | proved |  |
| Lemma 7.6 | 159 | For $\chi\ne\chi_1$: $L(1,\chi)\sum_{p\le x}\chi(p)\log p/p$ is expressed through $L'(1,\chi)$ plus $O(1)$ (so $L(1,\chi)\ne0$ is the crux) | `NTKB.Apostol.lemma_7_6` | proved |  |
| Lemma 7.7 | 160 | Estimate for $\sum_{p\le x,\,p\equiv1}\log p/p$ in terms of $N(k)$, the number of nonprincipal $\chi$ with $L(1,\chi)=0$ | `NTKB.Apostol.lemma_7_7` | proved |  |
| Lemma 7.8 | 160 | If $\chi\ne\chi_1$ and $L(1,\chi)=0$ then a $\chi$-weighted sum of $\Lambda(n)/n$ has a $\log x$ term with explicit coefficient (details in book) | `NTKB.Apostol.lemma_7_8` | proved |  |
| Theorem 7.9 | 164 | Dirichlet's theorem: infinitely many primes $\equiv h\pmod k$ when $(h,k)=1$ | `Nat.infinite_setOfPred_prime_and_modEq`, `Nat.forall_exists_prime_gt_and_modEq`, `Nat.infinite_setOfPred_prime_and_eq_mod`, `NTKB.Apostol.exists_prime_gt_eq` | in Mathlib |  |
| Theorem 7.10 | 165 | $\pi_a(x)\sim x/(\varphi(k)\log x)$ for all $a$ coprime to $k$ iff $\pi_a(x)\sim\pi_b(x)$ for all coprime $a,b$ | `NTKB.Apostol.apostol_thm_7_10`, `NTKB.Apostol.primeCountAP` | proved | Tau Ceti: `NumberField.Chebotarev.primeCount_primesCongruent_isEquivalent_logIntegral`, Tau Ceti: `NumberField.Chebotarev.hasNaturalDensity_primesCongruent` |

## Chapter 8

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 8.1 | 168 | $\sum_{m=0}^{k-1} e^{2\pi i mn/k}$ equals $k$ if $k\mid n$ and $0$ otherwise | `IsPrimitiveRoot.geom_sum_eq_zero`, `AddChar.sum_mulShift`, `AddChar.sum_eq_zero_of_ne_one`, `NTKB.Apostol.sum_range_eC`, `NTKB.Apostol.eC` | in Mathlib |  |
| Theorem 8.2 | 168 | Lagrange interpolation: for $k$ distinct nodes and values there is a unique polynomial of degree $<k$ through them | `Lagrange.interpolate`, `Lagrange.eq_interpolate`, `Lagrange.degree_interpolate_lt`, `Lagrange.eval_interpolate_at_node`, `Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq` | in Mathlib |  |
| Theorem 8.3 | 169 | Any $k$ complex values $w_m$ are uniquely $\sum_n a_n e^{2\pi i mn/k}$, with $a_n$ given by an explicit inverse sum | `ZMod.dft`, `ZMod.dft_dft`, `ZMod.invDFT_apply` | in Mathlib |  |
| Theorem 8.4 | 170 | A $k$-periodic arithmetical function has a unique $k$-periodic $g$ with $f(m)=\sum_n g(n)e^{2\pi i mn/k}$, $g(n)=\frac1k\sum_m f(m)e^{-2\pi i mn/k}$ | `ZMod.dft`, `ZMod.dft_apply`, `ZMod.invDFT_def'` | in Mathlib |  |
| Theorem 8.5 | 171 | $s_k(n)=\sum_{d\mid(n,k)} f(d)g(k/d)$ has finite Fourier expansion with coefficients $a_k(m)=\frac1k\sum_{d\mid (m,k)} f(k/d)g(d)\,d$ | `NTKB.Apostol.gcdSum_eq_fourier`, `NTKB.Apostol.gcdSum` | proved |  |
| Theorem 8.6 | 172 | Ramanujan's sum $c_k(n)=\sum_{d\mid(n,k)} d\,\mu(k/d)$ | `NTKB.Apostol.ramanujanSum_eq` | proved |  |
| Theorem 8.7 | 172 | For multiplicative $f,g$: $s_{mk}(ab)=s_m(a)s_k(b)$ if $(a,k)=(b,m)=1$, with two special cases; applies to $c_k$ | `NTKB.Apostol.gcdSum_mul_mul`, `NTKB.Apostol.ramanujanSum_mul_mul`, `NTKB.Apostol.ramanujanSum_counterexample_8_7` | proved |  |
| Theorem 8.8 | 173 | For completely multiplicative $f$ and $g=\mu h$ (with $f(p)\ne0$, $f(p)\ne h(p)$): $s_k(n)=F(k)g(N)/f(N)$, with $F=f*g$, $N=k/(n,k)$; gives $c_k(n)=\varphi(k)\mu(N)/\varphi(N)$ | `NTKB.Apostol.gcdSum_mul_eq`, `NTKB.Apostol.gcdSum_eq_div`, `NTKB.Apostol.ramanujanSum_eq_totient_mul_moebius_div` | proved |  |
| Theorem 8.9 | 175 | $G(n,\chi)=\bar\chi(n)G(1,\chi)$ when $(n,k)=1$ | `gaussSum_mulShift`, `gaussSum_mulShift_eq`, `NTKB.Apostol.gaussSumSeparable_of_isUnit`, `NTKB.Apostol.GaussSumSeparable` | in Mathlib |  |
| Theorem 8.10 | 176 | $G(n,\chi)$ separable for all $n$ iff $G(n,\chi)=0$ whenever $(n,k)>1$ | `NTKB.Apostol.gaussSumSeparable_forall_iff` | proved |  |
| Theorem 8.11 | 176 | If $G(n,\chi)$ separable for all $n$ then $\lvert G(1,\chi)\rvert^2=k$ | `NTKB.Apostol.apostol_thm_8_11` | proved | Tau Ceti: `IsPrimitive.norm_gaussSum`, Tau Ceti: `gaussSum_mul_gaussSum_inv_eq_card_of_isPrimitive` |
| Theorem 8.12 | 176 | If $G(n,\chi)\ne0$ for some $(n,k)>1$ then some proper divisor $d<k$ is an induced modulus | `DirichletCharacter.factorsThrough_of_gaussSum_ne_zero` | in Mathlib |  |
| Theorem 8.13 | 177 | $1$ is an induced modulus for $\chi$ iff $\chi$ is principal | `DirichletCharacter.eq_one_iff_conductor_eq_one`, `DirichletCharacter.conductor_one` | in Mathlib |  |
| Theorem 8.14 | 178 | Every nonprincipal character mod a prime is primitive | `NTKB.Apostol.isPrimitive_of_ne_one_of_prime` | proved |  |
| Theorem 8.15 | 178 | For primitive $\chi$ mod $k$: (a) $G(n,\chi)=0$ if $(n,k)>1$, (b) $G$ separable, (c) $\lvert G(1,\chi)\rvert^2=k$ | `DirichletCharacter.gaussSum_mulShift_of_isPrimitive`, `DirichletCharacter.gaussSum_eq_zero_of_isPrimitive_of_not_isPrimitive`, `IsPrimitive.norm_gaussSum`, `NTKB.Apostol.apostol_thm_8_11` | in Mathlib |  |
| Theorem 8.16 | 178 | $d\mid k$ is an induced modulus iff $\chi(a)=\chi(b)$ whenever $(ab,k)=1$ and $a\equiv b \pmod d$ | `NTKB.Apostol.factorsThrough_iff_apply_eq` | proved | Mathlib: `DirichletCharacter.factorsThrough_iff_ker_unitsMap`, Mathlib: `DirichletCharacter.changeLevel_eq_cast_of_dvd` |
| Theorem 8.17 | 179 | $d$ is an induced modulus iff $\chi=\psi\chi_1$ for a character $\psi$ mod $d$ and principal $\chi_1$ mod $k$ | `DirichletCharacter.FactorsThrough`, `DirichletCharacter.factorsThrough_iff_ker_unitsMap`, `DirichletCharacter.changeLevel` | in Mathlib |  |
| Theorem 8.18 | 181 | Every $\chi$ mod $k$ is $\psi\chi_1$ with $\psi$ primitive mod the conductor | `DirichletCharacter.primitiveCharacter`, `DirichletCharacter.changeLevel_primitiveCharacter`, `DirichletCharacter.primitiveCharacter_isPrimitive` | in Mathlib |  |
| Theorem 8.19 | 181 | $\chi$ is primitive iff $G(n,\chi)$ is separable for all $n$ | `NTKB.Apostol.isPrimitive_iff_forall_gaussSumSeparable`, `NTKB.Apostol.gaussSum_changeLevel_mulShift` | proved | Mathlib: `DirichletCharacter.gaussSum_mulShift_of_isPrimitive` |
| Theorem 8.20 | 182 | Finite Fourier expansion of a primitive $\chi$: $\chi(m)=\frac{\tau_k(\chi)}{k}\sum_n\bar\chi(n)e^{2\pi i mn/k}$ (with $\lvert\tau_k(\chi)\rvert=1$ after normalization) | `DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`, `DirichletCharacter.fourierTransform_eq_gaussSum_mulShift`, `NTKB.Apostol.eq_fourier_of_isPrimitive` | in Mathlib |  |
| Theorem 8.21 | 183 | Pólya's inequality: for primitive $\chi$ mod $k$, $\lvert\sum_{m\le x}\chi(m)\rvert<\sqrt k\log k$ | `NTKB.Apostol.polya` | proved | Tau Ceti: `DirichletCharacter.norm_sum_Icc_le_level` |
| Exercise 8.4 | 185 | If $(a,d)=1$ there is $m\equiv a \pmod d$ with $(m,n)=1$ | `ZMod.unitsMap_surjective` | in Mathlib |  |
| Exercise 8.16(a) | 186 | $G(k;mn)=G(km;n)G(kn;m)$ for $(m,n)=1$ for quadratic Gauss sums | `NTKB.Apostol.quadGaussSum_mul`, `NTKB.Apostol.quadGaussSum_prime_pow`, `NTKB.Apostol.quadGaussSum_prime_pow_even_odd` | proved | Tau Ceti: `sum_stdAddChar_dotProduct_mulVec_mul` |
| Definition (Gauss sum of a Dirichlet character) | 175 | $G(n,\chi)=\sum_{m\bmod k}\chi(m)e^{2\pi i mn/k}$ | `ZMod.stdAddChar` | in Mathlib |  |
| Definition (induced modulus, primitive character) | 177 | $d\mid k$ with $\chi(a)=1$ for $a\equiv1 \pmod d$, $(a,k)=1$; primitive = none with $d<k$ | `DirichletCharacter.FactorsThrough`, `DirichletCharacter.IsPrimitive` | in Mathlib |  |
| Definition (conductor) | 181 | Smallest induced modulus of $\chi$ | `DirichletCharacter.conductor`, `DirichletCharacter.conductorSet` | in Mathlib |  |
| Definition (Ramanujan sum) | 169 | $c_k(n)$ = sum of $n$-th powers of primitive $k$-th roots of unity | `NTKB.Apostol.ramanujanSum`, `NTKB.Apostol.gcdSum` | proved |  |
| Definition (Kloosterman sum) | 185 | $K(m,n;k)=\sum_{(h,k)=1} e^{2\pi i (mh+n\bar h)/k}$ | `NTKB.Apostol.kloosterman`, `NTKB.Apostol.kloosterman_comm`, `NTKB.Apostol.kloosterman_eq_one_mul` | proved |  |

## Chapter 9

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 9.1 | 189 | For an odd prime $p$ exactly $(p-1)/2$ residues and $(p-1)/2$ nonresidues mod $p$, represented by $1^2,\dots,((p-1)/2)^2$ | `NTKB.Apostol.card_nonzero_squares`, `NTKB.Apostol.card_nonsquares`, `NTKB.Apostol.squares_eq_image_sq_half` | proved | Mathlib: `legendreSym.card_sqrts`, Mathlib: `quadraticChar_sum_zero` |
| Theorem 9.2 | 190 | Euler's criterion: $\left(\frac np\right)\equiv n^{(p-1)/2} \pmod p$ | `legendreSym.eq_pow`, `ZMod.euler_criterion` | in Mathlib |  |
| Theorem 9.3 | 190 | The Legendre symbol is completely multiplicative in $n$ | `legendreSym.mul`, `legendreSym.hom` | in Mathlib |  |
| Theorem 9.4 | 191 | $\left(\frac{-1}p\right)=(-1)^{(p-1)/2}$ | `legendreSym.at_neg_one`, `ZMod.exists_sq_eq_neg_one_iff` | in Mathlib |  |
| Theorem 9.5 | 191 | $\left(\frac 2p\right)=(-1)^{(p^2-1)/8}$ | `legendreSym.at_two`, `ZMod.exists_sq_eq_two_iff` | in Mathlib |  |
| Theorem 9.6 | 192 | Gauss' lemma: $\left(\frac np\right)=(-1)^m$, $m$ = number of least residues of $n,2n,\dots$ exceeding $p/2$ | `ZMod.gauss_lemma`, `ZMod.gauss_lemma_aux` | in Mathlib |  |
| Theorem 9.7 | 193 | Parity of $m$: $m\equiv\sum_{t\le (p-1)/2}\lfloor tn/p\rfloor+(n-1)\frac{p^2-1}8 \pmod 2$; for odd $n$, $m\equiv\sum\lfloor tn/p\rfloor$ | `NTKB.Apostol.gauss_count_modEq` | proved | Mathlib: `ZMod.eisenstein_lemma_aux`, Mathlib: `ZMod.eisenstein_lemma` |
| Theorem 9.8 | 195 | Quadratic reciprocity: $\left(\frac pq\right)\left(\frac qp\right)=(-1)^{\frac{p-1}2\frac{q-1}2}$ | `legendreSym.quadratic_reciprocity`, `legendreSym.quadratic_reciprocity'`, `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three` | in Mathlib |  |
| Theorem 9.9 | 198 | Jacobi symbol: (a) multiplicative in $n$, (b) in $P$, (c) periodic mod $P$, (d) $(a^2n\mid P)=(n\mid P)$ for $(a,P)=1$ | `jacobiSym.mul_left`, `jacobiSym.mul_right`, `jacobiSym.mod_left'`, `jacobiSym.sq_one'` | in Mathlib |  |
| Theorem 9.10 | 198 | For odd $P>0$: $(-1\mid P)=(-1)^{(P-1)/2}$, $(2\mid P)=(-1)^{(P^2-1)/8}$ | `jacobiSym.at_neg_one`, `jacobiSym.at_two` | in Mathlib |  |
| Theorem 9.11 | 199 | Jacobi reciprocity for coprime odd positive $P,Q$ | `jacobiSym.quadratic_reciprocity`, `jacobiSym.quadratic_reciprocity'`, `jacobiSym.quadratic_reciprocity_if` | in Mathlib |  |
| Theorem 9.12 | 201 | $y^2=x^3+k$ has no integer solutions when $k=(4n-1)^3-4m^2$ and no prime $\equiv-1 \pmod 4$ divides $m$ | `NTKB.Apostol.sq_ne_cube_add` | proved |  |
| Theorem 9.13 | 202 | $G(1,\chi)^2=\left(\frac{-1}p\right)p$ for the quadratic character mod $p$ | `gaussSum_sq`, `quadraticChar_card_card` | in Mathlib |  |
| Theorem 9.14 | 203 | Reciprocity law is equivalent to $G(1,\chi)^{q-1}\equiv\left(\frac qp\right) \pmod q$ | `NTKB.Apostol.apostol_thm_9_14`, `NTKB.Apostol.gaussSum_pow_modEq`, `NTKB.Apostol.gaussSum_pow_eq` | proved | Mathlib: `MulChar.IsQuadratic.gaussSum_frob`, Mathlib: `MulChar.IsQuadratic.gaussSum_frob_iter`, Tau Ceti: `gaussSum_pow_char_pow` |
| Theorem 9.15 | 203 | $G(1,\chi)^q=\left(\frac qp\right)\sum_{r_1+\dots+r_q\equiv q}\left(\frac{r_1\cdots r_q}p\right)$ | `NTKB.Apostol.gaussSum_pow_eq_sum_tuples`, `NTKB.Apostol.sum_tuples_eq_mul_gaussSum_pow` | proved |  |
| Theorem 9.16 | 206 | $S(a,m)=\sqrt{m/a}\,e^{\pi i/4}\overline{S(m,a)}$ (reciprocity for $S(a,m)=\sum_{r<m}e^{\pi i ar^2/m}$) when $ma$ even | `NTKB.Apostol.apostol_thm_9_16`, `NTKB.Apostol.quadSumS` | proved | Tau Ceti: `sq_sum_range_cexp_two_pi_I_mul_sq_div` |
| Theorem 9.17 | 210 | $G(h;k)=\sqrt{k/2h}\,(1+e^{-\pi i hk/2})\sum_{r<h}e^{\pi i k r^2/2h}$ for $h$ odd, $h,k>0$ | `NTKB.Apostol.apostol_thm_9_17`, `NTKB.Apostol.gauss_formula` | proved |  |
| Definition (quadratic residue, Legendre symbol) | 188 | $n$ residue mod $p$ if $x^2\equiv n$ solvable; $\left(\frac np\right)=\pm1,0$ | `IsSquare` | in Mathlib |  |
| Definition (Jacobi symbol) | 198 | $(n\mid P)=\prod(n\mid p_i)^{a_i}$, $(n\mid1)=1$ | — | in Mathlib |  |
| Definition (quadratic Gauss sum $G(n;m)$) | 204 | $G(n;m)=\sum_{r\le m}e^{2\pi i n r^2/m}$ | `NTKB.Apostol.quadGaussSum`, `NTKB.Apostol.quadGaussSum_eq_sum_zmod` | proved | Tau Ceti: `sum_range_cexp_two_pi_I_sq_div` |

## Chapter 10

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 10.1 | 214 | For (a,m)=1 with exponent f: a^n=1 mod m iff f divides n; f divides phi(m); a^0..a^(f-1) pairwise incongruent | `orderOf_dvd_iff_pow_eq_one`, `orderOf_dvd_card`, `pow_injOn_Iio_orderOf`, `ZMod.pow_totient` | in Mathlib |  |
| Theorem 10.2 | 215 | a is a primitive root mod m iff a, a^2, ..., a^phi(m) form a reduced residue system | `orderOf_eq_card_of_forall_mem_zpowers`, `isCyclic_of_orderOf_eq_card`, `pow_injOn_Iio_orderOf` | in Mathlib |  |
| Theorem 10.3 | 216 | For odd x and a>=3, x^(phi(2^a)/2) = 1 mod 2^a, so no primitive roots mod 2^a | `NTKB.Apostol.pow_two_pow_sub_two_modEq_one` | proved | Mathlib: `ZMod.isCyclic_units_two_pow_iff`, Mathlib: `ZMod.not_isCyclic_units_eight`, Mathlib: `Int.eight_dvd_sq_sub_one_of_odd` |
| Lemma 1 | 216 | If a has exponent f mod m then a^k has exponent f/gcd(k,f); same exponent iff gcd(k,f)=1 | `orderOf_pow'`, `orderOf_pow_of_dvd` | in Mathlib |  |
| Theorem 10.4 | 217 | For odd prime p and d dividing p-1, exactly phi(d) residues mod p have exponent d; so phi(p-1) primitive roots | `IsCyclic.card_orderOf_eq_totient`, `ZMod.isCyclic_units_prime` | in Mathlib |  |
| Theorem 10.5 | 218 | For primitive root g mod odd prime p, even powers of g are the quadratic residues, odd powers the non-residues | `NTKB.Apostol.isSquare_pow_primitiveRoot_iff` | proved | Mathlib: `ZMod.euler_criterion`, Mathlib: `ZMod.euler_criterion_units` |
| Theorem 10.6 | 219 | (a) a primitive root g mod p is one mod p^a for all a iff g^(p-1) != 1 mod p^2; (b) such g exists, so primitive roots exist mod p^a | `NTKB.Apostol.orderOf_prime_pow_eq_totient_iff` | proved | Tau Ceti: `orderOf_conreyGenerator` |
| Lemma 2 | 220 | If g is a primitive root mod p with g^(p-1) != 1 mod p^2 then g^(p^(a-2)(p-1)) != 1 mod p^a for a>=2 | `NTKB.Apostol.ch10_lemma_2` | proved | Mathlib: `ZMod.orderOf_one_add_mul_prime_pow`, Mathlib: `ZMod.exists_one_add_mul_pow_prime_pow_eq` |
| Theorem 10.7 | 220 | For odd prime p, odd primitive roots mod p^a exist and each is a primitive root mod 2p^a | `ZMod.isCyclic_units_two_mul_iff_of_odd`, `ZMod.isCyclic_units_of_prime_pow` | in Mathlib |  |
| Theorem 10.8 | 221 | If m is not 1,2,4,p^a,2p^a (p odd prime) there are no primitive roots mod m | `ZMod.isCyclic_units_iff`, `ZMod.not_isCyclic_units_of_mul_coprime` | in Mathlib |  |
| Theorem 10.9 | 222 | If m has a primitive root g there are exactly phi(phi(m)) of them, namely g^n with gcd(n,phi(m))=1 | `IsCyclic.card_orderOf_eq_totient`, `orderOf_pow'` | in Mathlib |  |
| Theorem 10.10 | 224 | Index laws: ind(ab)=ind a+ind b, ind a^n = n ind a, ind 1=0, ind g=1, ind(-1)=phi(m)/2, change of base | `NTKB.Apostol.ind_mul`, `NTKB.Apostol.ind_pow`, `NTKB.Apostol.ind_one_and_ind_self`, `NTKB.Apostol.ind_self_of_two_lt`, `NTKB.Apostol.ind_neg_one`, `NTKB.Apostol.ind_change_base` | proved |  |
| Theorem 10.11 | 228 | For a>=3 every odd n is uniquely (-1)^e 5^b mod 2^a with 1<=b<=phi(2^a)/2 | `ZMod.isComplement'_zpowers_unitFive_neg_one`, `ZMod.orderOf_unitFive`, `ZMod.zpowers_mk_unitFive_eq_top` | in Mathlib |  |
| Theorem 10.12 | 230 | Exactly two real characters mod p^a (p odd) | `NTKB.Apostol.card_isQuadratic_prime_pow` | proved |  |
| Theorem 10.13 | 230 | Exactly four real characters mod 2^a for a>=3 | `NTKB.Apostol.card_isQuadratic_two_pow`, `NTKB.Apostol.isQuadratic_charAC_iff` | proved |  |
| Theorem 10.14 | 231 | Character chi_h mod p^a (a>=2) is primitive iff p does not divide h | `NTKB.Apostol.isPrimitive_charH_iff`, `NTKB.Apostol.charH`, `NTKB.Apostol.charH_apply` | proved |  |
| Theorem 10.15 | 231 | Character chi_{a,c} mod 2^a (a>=3) is primitive iff c odd | `NTKB.Apostol.isPrimitive_charAC_iff`, `NTKB.Apostol.charAC`, `NTKB.Apostol.fChar`, `NTKB.Apostol.gChar` | proved |  |
| Definition: exponent exp_m(a) | 214 | Least f>0 with a^f = 1 mod m | — | in Mathlib |  |
| Definition: primitive root mod m | 214 | a with exp_m(a)=phi(m) | `NTKB.Apostol.IsPrimitiveRootMod` | proved | Mathlib: `IsCyclic.exists_generator` |
| Definition: index ind_g a | 223 | The k with g^k = a mod m | `NTKB.Apostol.ind` | proved |  |

## Chapter 11

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 11.1 | 235 | A Dirichlet series has an abscissa of absolute convergence: absolutely convergent to the right, not to the left | `LSeries.abscissaOfAbsConv`, `LSeriesSummable_of_abscissaOfAbsConv_lt_re`, `LSeriesSummable.abscissaOfAbsConv_le` | in Mathlib |  |
| Theorem 11.2 | 236 | F(sigma+it) tends to f(1) as sigma to +infinity, uniformly in t | `NTKB.Apostol.apostol_thm_11_2` | proved | Mathlib: `LSeries.tendsto_atTop` |
| Lemma 1 (ch. 11) | 236 | Tail bound for sum_{n>=N} f(n)n^-s when sigma>c>sigma_a | `NTKB.Apostol.ch11_lemma_1` | proved |  |
| Theorem 11.3 | 237 | Uniqueness: if F=G at s_k with Re s_k to infinity then f=g | `NTKB.Apostol.apostol_thm_11_3` | proved | Mathlib: `LSeries_eq_iff_of_abscissaOfAbsConv_lt_top`, Mathlib: `LSeries_injOn`, Mathlib: `LSeries.eq_of_LSeries_eventually_eq` |
| Theorem 11.4 | 237 | A nonzero Dirichlet series has a half-plane where it is nowhere zero | `NTKB.Apostol.apostol_thm_11_4` | proved | Mathlib: `LSeries_eventually_eq_zero_iff'` |
| Theorem 11.5 | 238 | Product of Dirichlet series is the Dirichlet series of the convolution; converse along a sequence | `NTKB.Apostol.apostol_thm_11_5_converse` | proved | Mathlib: `LSeries_convolution`, Mathlib: `LSeries_convolution'`, Mathlib: `LSeries_mul` |
| Example 6 (ch. 11) | 239 | sum lambda(n) n^-s = zeta(2s)/zeta(s) via 1*lambda = indicator of squares | `NTKB.Apostol.LSeries_liouville` | proved | PNT+: `LSeries_liouville_eq` |
| Theorem 11.6 | 240 | Euler product for absolutely summable multiplicative f (simpler if completely multiplicative) | `EulerProduct.eulerProduct_hasProd`, `ArithmeticFunction.IsMultiplicative.eulerProduct_hasProd`, `EulerProduct.eulerProduct_completely_multiplicative_hasProd` | in Mathlib |  |
| Theorem 11.7 | 241 | Euler product for Dirichlet series with absolutely convergent coefficients | `NTKB.Apostol.apostol_thm_11_7`, `NTKB.Apostol.apostol_thm_11_7_completely` | proved | Mathlib: `riemannZeta_eulerProduct_hasProd`, Mathlib: `DirichletCharacter.LSeries_eulerProduct_hasProd` |
| Lemma 2 (ch. 11) | 242 | Bounded partial sums of f(n)n^-s0 bound blocks of f(n)n^-s for sigma>sigma0 | `NTKB.Apostol.ch11_lemma_2` | proved |  |
| Theorem 11.8 | 243 | If the series converges at s0 it converges for Re s>Re s0 | `NTKB.Apostol.apostol_thm_11_8` | proved | Tau Ceti: `LSeriesConverges.of_re_lt_re`, Tau Ceti: `LSeriesConverges.abscissaOfConv_le` |
| Theorem 11.9 | 243 | Abscissa of (conditional) convergence exists | `NTKB.Apostol.apostol_thm_11_9`, `NTKB.Apostol.ConvergesAt` | proved | Tau Ceti: `LSeries.abscissaOfConv`, Tau Ceti: `LSeriesConverges_of_abscissaOfConv_lt_re` |
| Theorem 11.10 | 244 | 0 <= sigma_a - sigma_c <= 1 | `NTKB.Apostol.apostol_thm_11_10` | proved | Tau Ceti: `LSeries.abscissaOfConv_le_abscissaOfAbsConv`, Tau Ceti: `LSeries.abscissaOfAbsConv_le_abscissaOfConv_add_one` |
| Lemma 3 | 244 | Locally uniform limit of analytic functions is analytic and derivatives converge locally uniformly | `TendstoLocallyUniformlyOn.differentiableOn`, `TendstoLocallyUniformlyOn.deriv` | in Mathlib |  |
| Theorem 11.11 | 245 | Dirichlet series converges uniformly on compacts inside the half-plane of convergence | `NTKB.Apostol.apostol_thm_11_11` | proved |  |
| Theorem 11.12 | 246 | Sum function is analytic in half-plane of convergence; derivative termwise | `NTKB.Apostol.apostol_thm_11_12` | proved | Mathlib: `LSeries_differentiableOn`, Mathlib: `LSeries_hasDerivAt`, Mathlib: `LSeries_deriv` |
| Theorem 11.13 | 247 | Landau: nonnegative coefficients, and the sum function analytic at the real abscissa of convergence, imply convergence further left (contrapositive: no analytic extension across the abscissa) | `landau_of_abscissaOfConv` | in Tau Ceti only (not a dependency) |  |
| Theorem 11.14 | 248 | F(s)=exp(G(s)) with G = sum (f' * f^-1)(n)/log n * n^-s when F nonzero | `NTKB.Apostol.apostol_thm_11_14` | proved in part | Mathlib: `ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log`, Mathlib: `DirichletCharacter.LSeries_eulerProduct_exp_log`, Tau Ceti: `exp_tsum_neg_log_one_sub_eq_LSeries` |
| Theorem 11.15 | 250 | Cross product formula for two Dirichlet series: limit of mean of F(a+it) times conjugate G(b+it) equals a coefficient sum | `NTKB.Apostol.apostol_thm_11_15` | proved |  |
| Theorem 11.16 | 251 | Mean square: (1/2T) integral \\| F(sigma+it) \\| ^2 dt tends to sum \\| f(n) \\| ^2 n^-2sigma | `NTKB.Apostol.apostol_thm_11_16`, `NTKB.Apostol.apostol_thm_11_16_a`, `NTKB.Apostol.apostol_thm_11_16_b`, `NTKB.Apostol.apostol_thm_11_16_c`, `NTKB.Apostol.apostol_thm_11_16_d`, `NTKB.Apostol.LSeries_moebiusSq`, `NTKB.Apostol.LSeries_divisorSq` | proved |  |
| Theorem 11.17 | 252 | Mean value picks out a coefficient: limit of (1/2T) integral F(sigma+it) x^(it) dt | `NTKB.Apostol.apostol_thm_11_17`, `NTKB.Apostol.apostol_thm_11_17_of_ne` | proved |  |
| Lemma 4 | 253 | Truncated Perron kernel integral of a^z/z tends to 1, 1/2, 0 for a>1, a=1, a<1, with error bounds | `tendsto_truncatedPerronKernel`, `tendsto_truncatedPerronKernel_one`, `norm_truncatedPerronKernel_le_of_lt_one`, `norm_truncatedPerronKernel_sub_one_le_of_one_lt` | in Tau Ceti only (not a dependency) |  |
| Theorem 11.18 | 255 | Perron formula: truncated integral of F(s+z)x^z/z gives sum_{n<x} f(n)n^-s with half weight at integer x, with error | `tendsto_truncatedPerron_LSeries`, `norm_truncatedPerron_LSeries_sub_sum_le`, `tendsto_truncatedPerron_LSeries_natCast` | in Tau Ceti only (not a dependency) |  |
| Definition: Dirichlet series | 234 | Series sum f(n) n^-s | `LSeries`, `LSeriesSummable`, `NTKB.Apostol.dirichletPartialSum`, `NTKB.Apostol.dirichletSum` | in Mathlib |  |
| Definition: abscissa of absolute convergence | 235 | sigma_a, with -infinity / +infinity conventions | `LSeries.abscissaOfAbsConv` | in Mathlib |  |
| Definition: Riemann zeta (Dirichlet series form) | 235 | zeta(s)=sum n^-s for Re s>1 | `LSeries_zeta_eq_riemannZeta` | in Mathlib |  |
| Definition: abscissa of convergence sigma_c | 242 | Boundary of the half-plane of (conditional) convergence | `NTKB.Apostol.abscissaOfConv`, `NTKB.Apostol.halfPlaneOfConv` | proved | Tau Ceti: `LSeries.abscissaOfConv`, Tau Ceti: `LSeriesConverges` |

## Chapter 12

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Def 12.A (Hurwitz zeta, periodic zeta) | 259 | $\zeta(s,a)=\sum_{n\ge0}(n+a)^{-s}$ for $\sigma>1$, $F(x,s)=\sum_{n\ge1}e^{2\pi i nx}n^{-s}$ | `HurwitzZeta.hurwitzZeta`, `HurwitzZeta.expZeta`, `HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re` | in Mathlib |  |
| Theorem 12.1 | 261 | The series for $\zeta(s,a)$ converges absolutely for $\sigma>1$, locally uniformly for $\sigma>1+\delta$, so $\zeta(s,a)$ is analytic there | `HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re`, `HurwitzZeta.differentiableAt_hurwitzZeta` | in Mathlib |  |
| Theorem 12.2 | 261 | For $\sigma>1$: $\Gamma(s)\zeta(s,a)=\int_0^\infty x^{s-1}e^{-ax}/(1-e^{-x})\,dx$ | `NTKB.Apostol.apostol_thm_12_2` | proved |  |
| Theorem 12.3 | 263 | For $0<a\le1$ the contour integral $I(s,a)=\frac1{2\pi i}\int_C z^{s-1}e^{az}/(1-e^z)\,dz$ is entire and equals $\Gamma(1-s)^{-1}$-times-scaled $\zeta(s,a)$ for $\sigma>1$ | `NTKB.Apostol.apostol_thm_12_3`, `NTKB.Apostol.pi_mul_hankelI`, `NTKB.Apostol.hankelI` | proved |  |
| Theorem 12.4 | 265 | $\zeta(s,a)$ extends analytically to $\mathbb C$ except a simple pole at $s=1$ of residue 1 | `HurwitzZeta.differentiableAt_hurwitzZeta`, `HurwitzZeta.hurwitzZeta_residue_one` | in Mathlib |  |
| Theorem 12.5 | 265 | $\zeta(s)$ and $L(s,\chi_1)$ are analytic except a simple pole at $1$ (residue 1, resp. $\prod_{p\mid k}(1-1/p)$); $L(s,\chi)$ is entire for $\chi\ne\chi_1$ | `differentiableAt_riemannZeta`, `riemannZeta_residue_one`, `DirichletCharacter.differentiableAt_LFunction`, `DirichletCharacter.differentiable_LFunction`, `DirichletCharacter.LFunctionTrivChar_residue_one` | in Mathlib |  |
| Theorem 12.6 | 267 | Hurwitz's formula: $\zeta(1-s,a)=\frac{\Gamma(s)}{(2\pi)^s}\{e^{-\pi i s/2}F(a,s)+e^{\pi i s/2}F(-a,s)\}$ | `HurwitzZeta.hurwitzZeta_one_sub` | in Mathlib |  |
| Theorem 12.7 | 269 | $\zeta(1-s)=2(2\pi)^{-s}\Gamma(s)\cos(\pi s/2)\zeta(s)$ | `riemannZeta_one_sub` | in Mathlib |  |
| Theorem 12.8 | 271 | For $1\le h\le k$: $\zeta(1-s,h/k)=\frac{2\Gamma(s)}{(2\pi k)^s}\sum_{r=1}^k\cos(\pi s/2-2\pi rh/k)\,\zeta(s,r/k)$ | `NTKB.Apostol.apostol_thm_12_8` | proved | Mathlib: `HurwitzZeta.hurwitzZeta_one_sub`, Mathlib: `ZMod.LFunction_one_sub` |
| Theorem 12.9 | 272 | If $\chi=\psi\chi_1$ ($\psi$ mod $d$, $\chi_1$ principal mod $k$) then $L(s,\chi)=L(s,\psi)\prod_{p\mid k}(1-\psi(p)p^{-s})$ for all $s$ | `DirichletCharacter.LFunction_changeLevel` | in Mathlib |  |
| Theorem 12.10 | 272 | For primitive $\chi$ mod $k$, $\sigma>1$: $G(1,\chi)L(s,\chi)=\sum_{h=1}^k\chi(h)F(h/k,s)$ | `NTKB.Apostol.apostol_thm_12_10`, `NTKB.Apostol.apostol_thm_12_10_LSeries` | proved | Mathlib: `DirichletCharacter.gaussSum_mulShift_of_isPrimitive`, Mathlib: `ZMod.LFunction_one_sub` |
| Theorem 12.11 | 273 | Functional equation: for primitive $\chi$ mod $k$, $L(1-s,\chi)=\frac{k^{s-1}\Gamma(s)}{(2\pi)^s}\{e^{-\pi is/2}+\chi(-1)e^{\pi is/2}\}G(1,\chi)L(s,\bar\chi)$ | `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`, `ZMod.LFunction_one_sub` | in Mathlib |  |
| Def 12.C (Bernoulli polynomials, numbers) | 274 | $ze^{xz}/(e^z-1)=\sum B_n(x)z^n/n!$, $B_n=B_n(0)$ | `Polynomial.bernoulli`, `Polynomial.bernoulli_generating_function` | in Mathlib |  |
| Theorem 12.12 | 274 | $B_n(x)=\sum_{k=0}^n\binom nk B_kx^{n-k}$ | `Polynomial.bernoulli_def`, `Polynomial.coeff_bernoulli` | in Mathlib |  |
| Theorem 12.13 | 274 | $\zeta(-n,a)=-B_{n+1}(a)/(n+1)$ for integers $n\ge0$ | `NTKB.Apostol.hurwitzZeta_zero_eq`, `NTKB.Apostol.apostol_thm_12_13` | proved | Mathlib: `HurwitzZeta.hurwitzZeta_neg_nat` |
| Theorem 12.14 | 275 | $B_n(x+1)-B_n(x)=nx^{n-1}$ ($n\ge1$); hence $B_n(0)=B_n(1)$ for $n\ge2$ | `Polynomial.bernoulli_eval_one_add`, `Polynomial.bernoulli_eval_zero`, `Polynomial.bernoulli_eval_one`, `bernoulli_eq_bernoulli'_of_ne_one` | in Mathlib |  |
| Theorem 12.15 | 275 | Recursion $\sum_{k=0}^{n-1}\binom nkB_k=0$ for $n\ge2$ | `sum_bernoulli` | in Mathlib |  |
| Theorem 12.16 | 276 | $\zeta(-n)=-B_{n+1}/(n+1)$ ($n\ge0$), $\zeta(-2k)=0$, $B_{2n+1}=0$ ($n\ge1$) | `riemannZeta_neg_nat_eq_bernoulli`, `riemannZeta_neg_two_mul_nat_add_one`, `bernoulli_eq_zero_of_odd` | in Mathlib |  |
| Theorem 12.17 | 276 | $\zeta(2k)=(-1)^{k-1}\frac{(2\pi)^{2k}B_{2k}}{2(2k)!}$ | `riemannZeta_two_mul_nat`, `hasSum_zeta_nat` | in Mathlib |  |
| Theorem 12.18 | 277 | $(-1)^{k+1}B_{2k}>0$ and $ \\| B_{2k} \\| \sim 2(2k)!/(2\pi)^{2k}$ | `NTKB.Apostol.neg_one_pow_mul_bernoulli_pos`, `NTKB.Apostol.tendsto_abs_bernoulli_div` | proved |  |
| Def 12.D (Bernoulli periodic function) | 277 | $\bar B_n(x)=B_n(x-\lfloor x\rfloor)$ | — | in Mathlib |  |
| Theorem 12.19 | 277 | Fourier series: $\sum_{k\ge1}\cos(2\pi kx)/k^{2n}=(-1)^{n-1}(2\pi)^{2n}B_{2n}(x)/(2(2n)!)$ on $[0,1]$ (and sine analogue for odd index) | `hasSum_one_div_nat_pow_mul_cos`, `hasSum_one_div_nat_pow_mul_sin`, `hasSum_one_div_nat_pow_mul_fourier` | in Mathlib |  |
| Theorem 12.20 | 278 | $L(0,\chi_1)=0$; for $\chi\ne\chi_1$, $L(0,\chi)=-\frac1k\sum_{r=1}^k r\chi(r)$ | `NTKB.Apostol.LFunction_one_zero`, `NTKB.Apostol.LFunction_zero_of_ne_one`, `NTKB.Apostol.LFunction_zero_of_even` | proved | Mathlib: `ZMod.LFunction_apply_zero_of_even`, Tau Ceti: `DirichletCharacter.generalizedBernoulli_one_of_ne_one` |
| Theorem 12.21 | 279 | Euler summation for $\zeta(s,a)$: $\zeta(s,a)=\sum_{n<N}(n+a)^{-s}+\frac{(N+a)^{1-s}}{s-1}+\frac{(N+a)^{-s}}2+s\int_N^\infty\frac{\lfloor x\rfloor-x+1/2}{(x+a)^{s+1}}dx$, $\sigma>0$ | `NTKB.Apostol.apostol_thm_12_21` | proved | PNT+: `Zeta0EqZeta`, PNT+: `riemannZeta0_apply` |
| Theorem 12.22 | 279 | Higher-order Euler-Maclaurin type expansion of $\zeta(s,a)$ with Bernoulli numbers up to $B_{m}$, valid for $\sigma>-m$ | `NTKB.Apostol.apostol_thm_12_22`, `NTKB.Apostol.apostol_thm_12_22_general` | proved |  |
| Theorem 12.23 | 280 | Bounds: $ \\| \zeta(s,a)-a^{-s} \\| \le\zeta(1+\delta)$ for $\sigma\ge1+\delta$, and $O( \\| t \\| ^{\delta})$, $O( \\| t \\| ^{1+\delta})$, $O( \\| t \\| ^{m+1+\delta})$ in the strips near $\sigma=1,0,-m$ | `NTKB.Apostol.apostol_thm_12_23_a`, `NTKB.Apostol.apostol_thm_12_23_b`, `NTKB.Apostol.apostol_thm_12_23_b'`, `NTKB.Apostol.apostol_thm_12_23_b''` | proved |  |
| Theorem 12.24 | 282 | $L(s,\chi)$ polynomial bounds in $t$ and $k$ in strips $ \\| \sigma+m \\| <\delta$ ($m\ge0$) | `NTKB.Apostol.apostol_thm_12_24`, `NTKB.Apostol.apostol_thm_12_24_pos` | proved | Tau Ceti: `DirichletCharacter.norm_LFunction_le_level_mul_norm_div_re`, Tau Ceti: `DirichletCharacter.LFunction_eq_mul_integral` |

## Chapter 13

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Theorem 13.1 | 291 | $\psi_1(x)=\sum_{n<x}(x-n)\Lambda(n)=\int_1^x\psi$; and $\psi_1(x)\sim x^2/2$ implies $\psi(x)\sim x$ | `NTKB.Apostol.psi1_eq_sum`, `NTKB.Apostol.tendsto_psi_div_of_psi1`, `NTKB.Apostol.psi1`, `NTKB.Apostol.sum_sub_mul_eq_partialSumIntegral`, `NTKB.Apostol.tendsto_partialSum_div_of_partialSumIntegral` | proved |  |
| Theorem 13.2 | 293 | For $c>1$, $x\ge1$: $\psi_1(x)/x^2=\frac1{2\pi i}\int_{c-i\infty}^{c+i\infty}\frac{x^{s-1}}{s(s+1)}\bigl(-\frac{\zeta'(s)}{\zeta(s)}\bigr)ds$ | `NTKB.Apostol.apostol_thm_13_2`, `NTKB.Apostol.ch13_lemma_3` | proved |  |
| Theorem 13.3 | 294 | For $c>1$, $x\ge1$: $\psi_1(x)/x^2-1/2=\frac1{2\pi i}\int_{c-i\infty}^{c+i\infty}x^{s-1}h(s)\,ds$ with $h(s)=\frac1{s(s+1)}(-\zeta'/\zeta-1/(s-1))$-type kernel | `NTKB.Apostol.apostol_thm_13_3` | proved |  |
| Theorem 13.4 | 295 | For each $A>0$ there is $M$ with $ \\| \zeta(s) \\| <M\log t$, $ \\| \zeta'(s) \\| <M\log^2t$ when $\sigma>1-A/\log t$, $t\ge e$ | `NTKB.Apostol.apostol_thm_13_4` | proved | PNT+: `ZetaUpperBnd`, PNT+: `ZetaDerivUpperBnd` |
| Theorem 13.5 | 296 | For $\sigma>1$: $ \\| \zeta(\sigma)^3\zeta(\sigma+it)^4\zeta(\sigma+2it) \\| \ge1$ | `DirichletCharacter.norm_LSeries_product_ge_one`, `norm_zeta_product_ge_one` | in Mathlib |  |
| Theorem 13.6 | 297 | $\zeta(1+it)\ne0$ for every real $t$ | `riemannZeta_ne_zero_of_one_le_re`, `DirichletCharacter.LFunction_ne_zero_of_re_eq_one`, `ZetaNoZerosOn1Line` | in Mathlib |  |
| Theorem 13.7 | 297 | For $\sigma\ge1$, $t\ge e$: $ \\| 1/\zeta(s) \\| <M\log^7t$ and $ \\| \zeta'(s)/\zeta(s) \\| <M\log^9t$ | `NTKB.Apostol.apostol_thm_13_7`, `NTKB.Apostol.one_le_norm_zeta_product` | proved | PNT+: `ZetaInvBnd`, PNT+: `LogDerivZetaBnd` |
| Lemma 4 (before 13.8) | 298 | If $f$ has a pole of order $k$ at $a$ then $f'/f$ has a simple pole with residue $-k$ | `NTKB.Apostol.logDeriv_eq_of_pole`, `NTKB.Apostol.logDeriv_eq_of_meromorphicOrderAt` | proved |  |
| Theorem 13.8 | 299 | $-\zeta'(s)/\zeta(s)-1/(s-1)$ is analytic at $s=1$ | `log_deriv_riemannZeta_eq_neg_inv_sub_add`, `log_deriv_riemannZeta_add_inv_sub_bounded` | in Mathlib |  |
| Theorem 13.9 | 299 | For $x>1$ the contour integral for $\psi_1$ tends to give $\psi_1(x)\sim x^2/2$ (Riemann-Lebesgue), completing the PNT | `NTKB.Apostol.apostol_thm_13_9`, `NTKB.Apostol.apostol_thm_13_9_integral`, `NTKB.Apostol.prime_number_theorem_psi`, `NTKB.Apostol.prime_number_theorem` | proved |  |
| Theorem 13.10 | 301 | Zero-free region: $ \\| \zeta(\sigma+it) \\| >C/\log^7t$ for $1-A/\log^9t<\sigma<1$, $t>e$; so $\zeta\ne0$ there | `ZetaLowerBnd`, `ZetaZeroFree9` | in PrimeNumberTheoremAnd only (not a dependency) |  |
| Def 13.A (trivial zeros) | 302 | the zeros $-2,-4,\dots$ of $\zeta$ are called trivial zeros | `riemannZeta_neg_two_mul_nat_add_one`, `riemannZeta_eq_zero_iff_of_re_nonpos` | in Mathlib |  |
| Theorem 13.11 | 302 | For $\sigma>0$: $(1-2^{1-s})\zeta(s)=\sum(-1)^{n-1}n^{-s}$; hence $\zeta(s)<0$ for real $0<s<1$ | `NTKB.Apostol.tendsto_sum_alternating_zeta`, `NTKB.Apostol.riemannZeta_neg_of_lt_one` | proved |  |
| Theorem 13.12 | 304 | $d(n)<2^{(1+\varepsilon)\log n/\log\log n}$ for large $n$ (a); infinitely often $>2^{(1-\varepsilon)\ldots}$ (b); consequently $d(n)=O(n^\delta)$ | `NTKB.Apostol.apostol_thm_13_12_a`, `NTKB.Apostol.apostol_thm_13_12_b'`, `NTKB.Apostol.apostol_thm_13_12_b` | proved | Tau Ceti: `TauCeti.exists_pos_card_divisors_le_rpow` |
| Theorem 13.13 | 307 | $\prod_{p\le x}(1-1/p)=c/\log x+O(1/\log^2x)$ with $c=e^{-\gamma}$ | `NTKB.Apostol.apostol_thm_13_13`, `NTKB.Apostol.mertensProd` | proved | PNT+: `Mertens.E₃.bound''`, PNT+: `Mertens.E₃.bound'''`, PNT+: `Mertens.M.eq` |
| Theorem 13.14 | 308 | $\varphi(n)>(1-\varepsilon)\,c\,n/\log\log n$ for large $n$ (a); $\varphi(n)<(1+\varepsilon)\ldots$ infinitely often (b) | `NTKB.Apostol.apostol_thm_13_14`, `NTKB.Apostol.apostol_thm_13_14'` | proved |  |
| Theorem 13.15 | 309 | Polya-type bound: for nonprincipal $\chi$ mod $k$, $ \\| \sum_{m\le x}\chi(m) \\| =O(\sqrt k\log k)$ | `NTKB.Apostol.apostol_thm_13_15`, `NTKB.Apostol.sum_changeLevel_eq`, `NTKB.Apostol.card_divisors_le_two_sqrt` | proved | Tau Ceti: `DirichletCharacter.norm_sum_Icc_le_level` |

## Chapter 14

| Item | Page | Statement | Lean declaration | Status | Also in |
|---|---|---|---|---|---|
| Def 14.A (partition, parts, $p(n)$, conjugate) | 317 | A partition of $n$ is a multiset of positive parts summing to $n$; $p(n)$ counts them; conjugate partitions via Ferrers graphs | `Nat.Partition`, `Nat.Partition.conjugate`, `Nat.Partition.conjugate_conjugate` | in Mathlib |  |
| Theorem 14.1 | 317 | Number of partitions of $n$ into exactly $m$ parts equals number with largest part $m$ | `NTKB.Apostol.card_partition_card_parts_eq` | proved | Mathlib: `Nat.Partition.conjugate` |
| Theorem 14.2 | 318 | Euler: for $ \\| x \\| <1$, $\prod_{m\ge1}(1-x^m)^{-1}=\sum_{n\ge0}p(n)x^n$ | `NTKB.Apostol.hasProd_partitionSeries`, `NTKB.Apostol.partitionSeries_mul_tprod_one_sub_X_pow`, `NTKB.Apostol.partitionSeries_mul_pentagonalSeries`, `NTKB.Apostol.partitionSeries` | proved | Mathlib: `Nat.Partition.hasProd_powerSeriesMk_card_restricted`, Mathlib: `Nat.Partition.hasProd_genFun`, Mathlib: `Nat.Partition.genFun_eq_tprod` |
| Def 14.B (generating function) | 318 | $F(x)=\sum f(n)x^n$ is the generating function of $f$ | `Nat.Partition.genFun` | in Mathlib |  |
| Theorem 14.3 | 322 | Euler's pentagonal number theorem: $\prod(1-x^m)=\sum_{k\in\mathbb Z}(-1)^kx^{k(3k-1)/2}$ for $ \\| x \\| <1$ | `eulerFunction_eq_tprod`, `eulerFunction_eq_tsum_pentagonal`, `hasSum_eulerFunction_pentagonal`, `PowerSeries.WithPiTopology.tprod_one_sub_X_pow` | in Mathlib |  |
| Def 14.C (power series of type $r$ mod $q$) | 338 | a power series $\sum a_nx^n$ with $a_n=0$ unless $n\equiv r\pmod q$ | `NTKB.Apostol.IsOfTypeMod` | proved |  |
| Theorem 14.4 | 325 | Recurrence $p(n)=p(n-1)+p(n-2)-p(n-5)-p(n-7)+\cdots$ | `NTKB.Apostol.sum_negOnePow_card_partition_sub_pentagonal` | proved |  |
| Theorem 14.5 | 326 | $p(n)<e^{K\sqrt n}$ with $K=\pi\sqrt{2/3}$ | `NTKB.Apostol.card_partition_lt_exp` | proved |  |
| Theorem 14.6 | 329 | Jacobi's triple product identity | `NTKB.Apostol.apostol_thm_14_6`, `NTKB.Apostol.jacobi_triple_product`, `NTKB.Apostol.qbinomial_theorem` | proved |  |
| Theorem 14.7 | 331 | $\prod(1-x^n)^3=\sum_{m\ge0}(-1)^m(2m+1)x^{m(m+1)/2}$ | `NTKB.Apostol.apostol_thm_14_7`, `NTKB.Apostol.jacobi_cube` | proved |  |
| Theorem 14.8 | 333 | For $F_A(x)=\prod_{n\in A}(1-x^n)^{-f(n)/n}=\sum p_{A,f}(n)x^n$: $np_{A,f}(n)=\sum_{k=1}^n f_A(k)p_{A,f}(n-k)$ with $f_A(k)=\sum_{d\mid k,d\in A}f(d)$ | `NTKB.Apostol.apostol_thm_14_8`, `NTKB.Apostol.X_mul_derivative_genFunA`, `NTKB.Apostol.mul_card_partition_eq_sum_sigma`, `NTKB.Apostol.genFunA`, `NTKB.Apostol.fA` | proved |  |
