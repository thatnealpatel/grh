# The one-prime orbital quotient over the rationals

**Scope:** Project calculations for $F=\mathbb Q$, the trivial $C_{\mathbb Q}^1$-isotype, and one rational prime $p$. Source readings are provisional and use `pdftotext -layout` of the [digest-matched edition](../sources/masullo/README.md). PDF ordinals match the printed pages cited below. No Lean declaration or visual reading is claimed.

## Which quotient is closed?

**Source interface.** Theorem 7.4.2.1, p. 367, (7.4.2.1), uses the global theta image modulo the actual range of $PV_p$. The operator is the uniformizer difference on the trivial isotype by (5.3.1.1), (5.3.1.5), and (5.3.1.10), pp. 240–242. The zero-line completion in (11.2.0.2)–(11.2.0.4), pp. 484–485, asserts that the completed range equals the actual range of the extended operator, which is claimed to be closed for $s\ge2|S_0|$. Equation (11.2.2.1), p. 489, uses the latter range to define its orbital Hilbert quotient. The global norm in (9.1.2.3), p. 399, and its disintegration on p. 400 give the following test of that identification. Compact averaging commutes with $PV_p$, so its radial range is the intersection of the global range with the closed radial subspace. In the proof on p. 485, the continuous Mellin functionals detect **closure**, not the exact image: In this isotype they are the circle Fourier coefficients of the periodization below.

Put $x=\log|g|_{\mathbb Q}$, $L=\log p$, and $H_s=L^2(\mathbb R,(1+x^2)^{s/2}\,dx)$. Constants from the compact Haar factor do not affect the topology. On radial functions the inserted uniformizer has norm $p^{-1}$, so $PV_p$ acts by $D f(x)=f(x)-f(x+L)$. The global radial theta image is dense in $H_s$ (see below). Translation is bounded for this polynomial weight, and $D$ is injective: A nonzero $L$-periodic function cannot be in $H_s$ for $s\ge0$. But $D$ is not bounded below. For nonzero $\eta\in C_c^\infty((1,2))$, put $f_R(x)=\eta(x/R)$, $R\to\infty$. Its squared norm is comparable to $R^{s+1}$. The difference is bounded pointwise by $L\|\eta'\|_\infty/R$ and supported in $[R-L,2R]$, so $\|D f_R\|_{H_s}/\|f_R\|_{H_s}=O(L/R)$. The bounded inverse theorem therefore rules out closedness of the actual range, including for $s\ge2$. This does not test the closedness assertion in the original theta topology of Chapter 7.

**Project repair on the zero line.** For $s>1$, write $P f([x])=\sum_{j\in\mathbb Z}f(x+jL)$ on the circle $\mathbb R/L\mathbb Z$. On a fundamental interval the sum of reciprocal weights is uniformly bounded; Cauchy–Schwarz yields a bounded map $H_s\to L^2(\mathbb R/L\mathbb Z,dx)$ and absolute summation for almost every $x$. Choose $w\in C_c^\infty(\mathbb R)$ with $P w=1$ by dividing a bump positive on a fundamental interval by its periodic sum. The section $u\mapsto w(x)u([x])$ is bounded and sends smooth inputs to smooth compactly supported ones. The kernel of $P$ is $\overline{D H_s}$: Approximate a kernel element by smooth compactly supported functions and subtract the section applied to their periodizations. Every smooth compactly supported $b$ of zero periodization is $D(\sum_{j\ge0}b(x+jL))$; using $-\sum_{j<0}b(x+jL)$ at the other end makes the primitive compactly supported. Since $P D=0$, the claimed closure follows. Thus the Hausdorff completion uses the **closure** of the range and is isomorphic, with equivalent Hilbert norms, to the circle. A bounded isomorphism suffices for the trace; it need not identify an orthogonal projection. Neither this repair nor the estimate on $D$ identifies a Paley–Wiener level.

**A consequence for the cutoff carvings.** Theorem 11.1.2.1(2), p. 480, uses closures in (11.1.2.6) taken *after* multiplying by $\rho_{\Lambda,+}$ or $\rho_\Lambda$ from (9.3.3.4)–(9.3.3.5), p. 428. Take $S$ to contain only the infinite place and take $S_i=\varnothing$, $S_{i'}=\{p\}$. Let $E$ denote the radial theta image. In both cases the indicator vanishes below $x=-\log\Lambda$. Shift the compactly supported section $J:u\mapsto wu$ by a sufficiently negative integer multiple of $L$, so $PJ=\operatorname{Id}$ and $M_\rho J=0$. For any $f\in H_s$, $f-JPf\in\ker P$ and $M_\rho(f-JPf)=M_\rho f$. Since $DE$ is dense in $\ker P$, it follows that $\overline{M_\rho DE}=M_\rho H_s=\overline{M_\rho E}$. Here $M_\rho H_s$ is closed because the indicator defines a projection. In this case the cutoff inclusion is never strict, although the uncut closure inclusion is strict by surjectivity of $P$. This tests the strictness claim for the specified indicator cutoffs, not an independent construction on a Paley–Wiener level.

For a direct proof on genuine inputs, including both telescopes and the effect of the global projections, see [the one-prime cut range](trace-cut-range-q.md). It does not require the ambient density or the section used above.

## Genuine global theta lifts

On the positive real section with all finite components $1$, the global theta sum (2.2.3.1), pp. 81–82, of $b_\infty\otimes\mathbf1_{\widehat{\mathbb Z}}$ is

$$\Theta_B(x)=\sum_{k\ge1}B(x+\log k),\qquad B(x)=2b_\infty(e^x),$$

where $b_\infty$ is even. The two adelic moments vanish if $b_\infty(0)=0$ and $\int_{\mathbb R}b_\infty=0$. For even Schwartz functions with these moments, Poisson summation gives rapid decay in $x$ in both directions, also after log differentiation: At $t=e^x\to0$, use $t^{-1}\sum_{k\ne0}\widehat b_\infty(k/t)$, with neither zero mode present; at $t\to\infty$ use the original sum. For $\operatorname{Re}z>1$, summing the Mellin integrals gives

$$\int_{\mathbb R}\Theta_B(x)e^{zx}\,dx=\zeta(z)\int_{\mathbb R}B(x)e^{zx}\,dx.$$

Both sides extend to the zero line (the pole at $1$ cancels; at $-\infty$, $B(x)=O(e^{2x})$). Use $\zeta(i\omega)\ne0$ on the zero line, from the classical zero-free $1$-line and the zeta functional equation for $\omega\ne0$, and $\zeta(0)=-1/2$. The reciprocal on the zero line grows at most polynomially: Use the functional equation, Stirling's estimate, and the reciprocal bound on the $1$-line, for which Masullo states a bound in Theorem B.6.1.6, (B.6.1.22), p. 640; see also [Leong, arXiv:2405.04869v3](https://arxiv.org/abs/2405.04869v3), §1.2, unconditional bound for $1/\zeta(1+it)$. These are classical zeta inputs, not consequences of the trace formula.

**Density used above.** For every real $\omega$, pick $B$ smooth and compactly supported with $\int B(x)e^{i\omega x}\,dx\ne0$ and $\int B(x)e^x\,dx=0$: Start with a narrow bump $b$ whose first integral is nonzero. Choose a nonzero real $d$ and set $B(x)=b(x)-e^d b(x+d)$; its Fourier multiplier $1-e^{d-i\omega d}$ cannot vanish. This gives a theta vector with nonzero Fourier transform near that frequency. If a vector of $H_s$ is orthogonal to the theta image, multiply its complex conjugate by the polynomial weight to obtain a tempered distribution. All translates of every theta vector are still in the image, so convolution of the distribution with each reflected theta vector is zero. On the Fourier side each multiplier is smooth and nonvanishing near its chosen frequency (use the opposite frequency for the reflection). The distribution vanishes on each such neighborhood and hence everywhere. This proves density without using the disputed closed-range step.

**Lift the circle modes.** Write $\omega_n=2\pi n/L$, $e_n([x])=L^{-1/2}e^{-i\omega_n x}$. Choose $q\in C_c^\infty(\mathbb R)$ with $\int e^x q(x)\,dx\ne0$, and put

$$B_n=w e_n-c_n Dq,\qquad c_n=\frac{\int e^x w(x)e_n([x])\,dx}{(1-e^{-L})\int e^x q(x)\,dx}.$$

The denominator is $\int e^x Dq(x)\,dx$. Thus $B_n$ has zero exponential moment, $P B_n=e_n$, and $b_{n,\infty}(y)=B_n(\log|y|)/2$, extended by zero near $0$, has the two required moments. All these real tests have support in a fixed compact set off $0$, and each fixed derivative seminorm grows at most polynomially in $|n|$. Comparing the circle Fourier coefficients via the Mellin identity gives $P\Theta_{B_n}=\zeta(i\omega_n)e_n$. In particular $v_n=\Theta_{B_n}/\zeta(i\omega_n)$ is a genuine global theta representative of $e_n$. Its $H_s$ norm grows at most polynomially: For $0<t\le1$ the Poisson sum is bounded by $C t\|b_{n,\infty}''\|_{L^1}$, by two integrations by parts and summation of $k^{-2}$; above $1$ use the fixed support and the bounded number of terms. Multiplying by $1/\zeta(i\omega_n)$ preserves a polynomial bound. For smooth circle inputs the Fourier series of the corresponding adelic test lifts converges in the even smooth real functions with that fixed compact support, tensored with $\mathbf1_{\widehat{\mathbb Z}}$. This is a continuous section into the original theta image as well.

**Exact kernel before completion.** Each trivial-isotype theta profile has a representative of the same form with an even Schwartz real component. In fact, every idele class has a unique representative with positive real component and finite components in $\widehat{\mathbb Z}^\times$: Multiply by the positive rational that clears the finite valuations, then choose its sign. Average a Schwartz–Bruhat representative over the finite units and the real sign. This preserves the theta profile in this isotype, as well as both moments. Now its finite factors are finite linear combinations of product balls $\mathbf1_{r\widehat{\mathbb Z}}$ with $r\in\mathbb Q_{>0}$ (radial locally constant functions at each active finite place are differences or sums of ball indicators). For a term with real component $g$, replace the finite ball by $\mathbf1_{\widehat{\mathbb Z}}$ and the real component by $g(r\,\cdot)$: The theta sum originally ranges over nonzero rationals in $r\mathbb Z$, and the finite ball's additive volume is $r^{-1}$ for $\operatorname{vol}(\widehat{\mathbb Z})=1$. Thus both moments agree after summing these replacements.

If $P\Theta_B=0$, the Mellin identity and zero-line nonvanishing give $P B=0$. For the even Schwartz real component $b_\infty$, solve the difference equation by

$$b_\infty^*(y)=\sum_{j\ge0}b_\infty(p^j y)=-\sum_{j<0}b_\infty(p^j y)\qquad(y\ne0).$$

The first series is Schwartz at infinity, with termwise derivatives. The second extends smoothly and evenly across $0$ with value zero: Use $b_\infty(y)=O(y^2)$ for the zeroth derivative and geometric factors $p^{jk}$ for derivatives of order $k\ge1$. The equation $b_\infty^*(y)-b_\infty^*(py)=b_\infty(y)$ implies $\int b_\infty^*=0$ by scaling. Theta summation intertwines the real difference with $D$, so the original theta profile is in the **actual** range there. Conversely $P D=0$. Periodization is continuous into smooth circle functions on the theta image: On each fixed Schwartz–Bruhat stage the finite reductions above are continuous, and the real Schwartz estimates for the differentiated theta sums are summable over period translates. The original theta quotient uses (7.4.0.2), p. 366, and the topology of (6.3.2.1), (6.3.2.5), pp. 303–304. Together with the section this gives the circle model of that exact quotient in this isotype. It does not equate the exact and closed ranges in the Hilbert completion, and does not rely on the Chapter 7 proof's citation of (11.2.2.12), p. 491.

## Trace, with a project position cutoff

Write $d\mu=d\mu^1\,du$ under $g=k\tau(e^u)$ and set $h_\varphi(u)=\int_{C_{\mathbb Q}^1}\varphi(k\tau(e^u))\,d\mu^1(k)$. Keep the raw compact Haar volume in $h_\varphi$; it is one for $\mathbb Q$ with the particular normalization (A.3.2.1), p. 560. Acting by left convolution with the test twisted by $|\cdot|^{-a}$ gives the circle multipliers

$$\lambda_n=\int_{\mathbb R}h_\varphi(u)e^{-a u+i\omega_n u}\,du.$$

Here $a=0$ matches (7.4.2.1), and $a=1/2$ inserts the twist of (11.3.2.5), p. 496. They are rapidly decreasing for any smooth compactly supported test, regardless of the sign of $u$ on its support. The multiplier operator is trace class on the Hilbert circle, and strongly nuclear on the smooth circle: After splitting $\lambda_n$ into two factors of modulus $\sqrt{|\lambda_n|}$, the output vectors are bounded in every smooth seminorm, the Fourier functionals are equicontinuous, and the remaining scalar sequence is in every $\ell^r$, $r>0$.

For a smooth compactly supported log-position cutoff $0\le\rho\le1$, take the chosen lifts **after** applying the circle convolution: Define $T_\rho e_n=\lambda_n P(\rho v_n)$. This gives an absolutely trace-norm summable rank-one expansion since $P$ is bounded, $\|v_n\|_{H_s}$ grows at most polynomially, and $\lambda_n$ decays rapidly. If $\rho\to1$ pointwise, each $\rho v_n\to v_n$ in $H_s$, and the same summable majorant gives trace-norm convergence. The limiting trace is

$$\sum_n\lambda_n=L\sum_{j\in\mathbb Z}e^{-ajL}h_\varphi(jL).$$

The factor $L$ results from periodizing $e^{-au}h_\varphi(u)$: Its $n$th circle coefficient with normalized Haar is $\lambda_n/L$, and one evaluates the Fourier series at $0$. This supplies a cutoff trace on both sides of norm one. For radial tests it is $L\,\mu^1(C_{\mathbb Q}^1)$ times the sum of the twisted test values at $p^j$, including negative $j$. If the entire support is strictly between $p^{-1}$ and $p$ and the test vanishes at norm one, the sum is zero.

**Limits of this comparison.** The cutoff above uses the exhibited section. Multiplying by an annular profile *before* passing to the quotient is not section-independent: For a nonconstant cutoff on some fiber, choose $f$ supported in a short interval where $\rho(x)\ne\rho(x-L)$. Then $P Df=0$ but $P(\rho Df)=P((\rho(x)-\rho(x-L))f(x))$ need not vanish. This is already an obstruction in the completed model; no cutoff descent is being asserted. Nor does this construction supply the actual Paley–Wiener level or identify any sector of the global diagonal with $T_\rho$.

In addition, the fixed trivial-isotype trace samples **compact averages**, not arbitrary point values on the orbit. The provisional text of Theorem 11.3.2.1, (11.3.2.1)–(11.3.2.5), pp. 495–496, assumes support above norm one and appears to pass from a fixed-character Mellin sum to unweighted point samples $\varphi(\pi_p^j)$ with coefficient $\log p/\mu_p(\mathbb Z_p^\times)$ (the unit-group superscript also appears in the raw text extraction). No Haar rescaling can convert one to the other on nonradial tests. For example, take $h\ge0$ supported in a short interval around $L$, with $h(L)>0$. With respect to the real norm section, choose a proper compact open subset $W$ of the norm-one group containing the compact component of $[\pi_p^{-1}]$. Then $\varphi(k\tau(e^u))=h(u)(1-\mathbf1_W(k))$ has zero point samples but positive averaged trace. One may take $W$ from a unit congruence at an odd prime $\ell\ne p$ included in $S$, making the test invariant by units outside $S$. This distinguishes the two expressions in the asserted Poisson step, not a sum over all compact characters: The global kernel of Definition 10.4.3.7, pp. 473–474, includes all isotypes, whereas (11.3.2.5) explicitly uses a fixed character and includes no outer sum. Such a sum could recover point evaluation with the correct angular phases. Even on radial tests, (11.3.2.5) gives a factor $e^{-jL/2}$ at log norm $jL$, absent from the point samples in (11.3.2.1). Neither issue by itself refutes an independently reconstructed identity for the global kernel. In particular both sums vanish under the Chapter 12 size bound $p>T$ for tests supported in $T^{-1}<|g|<T$ and vanishing at norm one. Before comparing with the partitioned global diagonal, establish the angular character bookkeeping, a lift other than the literal null indentation noted in the [geometric handoff](trace-geometric.md#integrating-the-stratum-split-is-not-evaluating-its-parts), and a comparison with the actual Paley–Wiener cutoff, not just the repaired circle trace.

**Review status:** Independent Yah checks used the digest-matched text for the source interfaces and separately challenged the density, exact theta kernel, adelic lifts, and trace-norm limit. Neither review was visual or a Lean check.

## Angular Poisson summation at one prime

**Source interfaces (provisional; independently checked in Yah against the digest-matched extraction).** Theorem 7.4.2.1, (7.4.2.1), p. 367, is a fixed-character statement with no half twist. In Theorem 11.3.2.1, pp. 495–496, (11.3.2.5) is still a fixed-character Mellin sum, but now the exponent is $\varepsilon_p-1/2$. Both layout and raw text show unweighted values $\varphi(\pi_p^k)$ in (11.3.2.1) for the rational one-place case. The cited Proposition B.4.1.2, (B.4.1.6)–(B.4.1.7), p. 608, is a log-lattice Poisson formula with a phase, and (B.4.1.20), p. 611, also shows a phase in the local-Euler case. The calculation here uses ordinary Fourier series of smooth periodizations to check the phase and weight directly. It evaluates the right side of (11.3.2.5), not the kernel appearing in (11.3.2.1).

The orbital branch is meant to use $p\notin S$: The restriction sets are disjoint from $S$ in (11.3.1.2), p. 492, and the application on p. 520 sums only over primes outside $S$. Page 493 says “the first $k$ rational primes” without this exclusion, which leaves the enumeration ambiguous when $S$ contains a finite prime. The examples below at $p=2$, $S=\{\infty,5\}$, avoid that ambiguity; $2$ is the first prime in either enumeration. The extra bound $p>T$ from p. 520 is not a test hypothesis of Theorem 11.3.2.1.

**Project calculation.** Write $C_{\mathbb Q}=K\times\mathbb R$ with $K=C_{\mathbb Q}^1\simeq\widehat{\mathbb Z}^{\times}$ and real coordinate $x=\log|g|_{\mathbb Q}$. The splitting uses the positive real section with all finite components $1$. Let $V=\mu^1(K)$ and let $\pi$ be the class of a uniformizer idele at $p$, so $\pi=(\kappa,-L)$ for $L=\log p$. Write $U_p\subset K$ for the image of $\mathbb Z_p^\times$. For $\eta\in\widehat K$ use the extension $\chi(k,x)=\eta(k)$; any norm-character factor in the extension is absorbed by shifting the Mellin parameter. On the $p$-unramified components the reciprocal Euler factor is $1-\eta(\kappa)e^{-zL}$, with simple zeros $z=i(\theta_\eta+2\pi n)/L$, $n\in\mathbb Z$, where $e^{i\theta_\eta}=\eta(\kappa)$. If $\eta|_{U_p}\ne 1$, the Euler factor is $1$ and there are no zeros, in agreement with $PV_p$ being the identity on the ramified local isotypes in (5.3.1.5), p. 241.

For $h_\eta(x)=\int_K\varphi(k,x)\eta(k)\,d\mu^1(k)$ and real twist $a$, the fixed-character sum is

$$
\sum_{n\in\mathbb Z}\int_{\mathbb R} h_\eta(x)e^{-a x+i(\theta_\eta+2\pi n)x/L}\,dx
= L\sum_{j\in\mathbb Z} e^{-ajL}\eta(\kappa)^j h_\eta(jL).
$$

Indeed the integrals are $L$ times the Fourier coefficients, in the positive-sign coefficient convention, of the $L$-periodization of $e^{-a x+i\theta_\eta x/L}h_\eta(x)$. Smoothness gives absolute Fourier convergence and allows evaluation at $0$. The phase is $\eta(\kappa)^j$, not its inverse: It pairs with $\eta(k)$ so that the angular point selected by inversion is $k=\kappa^{-j}$ at log norm $jL$.

There are only finitely many contributing angular characters. A smooth compactly supported test on $K\times\mathbb R$ factors through a finite quotient $K/N$ in the angular variable, taking a common open subgroup $N$ by compactness. Take $N$ to contain the outside-$S$ units $U^S$ if the test is invariant under them. The other characters have $h_\eta=0$. With $A_{U_p}\varphi(g)=\int_{U_p}\varphi(ug)\,du$ using probability Haar on $U_p$, sum the fixed-character expressions for all characters of $K/(NU_p)$. Their finite sum at $k\kappa^j$ is $[K:NU_p]\,\mathbf1_{NU_p}(k\kappa^j)$. The coset has raw volume $V/[K:NU_p]$, and averaging over it is equivalent to averaging over $U_p$ by $N$-invariance. Thus the summed comb is

$$
L V\sum_{j\in\mathbb Z} e^{-ajL}\,(A_{U_p}\varphi)(\pi^{-j})
= L V\sum_{m\in\mathbb Z} |\pi^m|_{\mathbb Q}^{-a}\,(A_{U_p}\varphi)(\pi^m).
$$

This expression is independent of the choice of uniformizer, even for a test not invariant by $U_p$. When $p\notin S$, $U_p\subset U^S$ and the average is the point evaluation. The raw volume $V$ and $\mu_p(\mathbb Z_p^\times)$ both equal one over $\mathbb Q$ by (A.3.2.1)–(A.3.2.2), p. 560. Thus in an untwisted sum over all contributing characters with $p\notin S$, the coefficient and samples agree with the displayed comb. Summing the **half-twisted** expressions does not remove the factor $|\pi^m|_{\mathbb Q}^{-1/2}$.

**Checks on the distinction.** With $p=2$, $S=\{\infty,5\}$, and the uniformizer $2$ at the $2$-slot, $\kappa$ has $5$-slot $2^{-1}\equiv3\pmod5$ after clearing the $2$-valuation. For a test supported in log norm near $L$ and angular class $2\bmod5$, the phase at $j=1$ selects that class: $2\cdot3=1\bmod5$. Omitting the phase selects class $1$; reversing it selects class $3$. For the twist discrepancy alone, take a radial bump supported in $(L-\delta,L+\delta)$ with $0<\delta<L/2$ and value $1$ at $L$. It satisfies the support-above-one assumption of Theorem 11.3.2.1 and is invariant under all units. Only the trivial angular character survives, yielding $L p^{-1/2}$ from (11.3.2.5) with $a=1/2$, versus $L$ from the extracted unweighted comb. Outside that orbital branch, if $p\in S$ and the test is not invariant under $U_p$, point evaluation is a second, separate discrepancy for the summed expressions: With $S=\{\infty,p\}$ and the same radial bump, multiply by an angular factor $\mathbf1_W-\mu_{U_p}(W)$, where $W$ is a proper open subgroup of the $p$-unit slot and $\mu_{U_p}$ is its probability Haar measure. At $\pi^{-1}$ for the inserted rational uniformizer $p$, the $p$-unit slot is $1$, so the sample is nonzero but the average is zero. The Chapter 12 application on p. 520 only uses primes outside $S$ with $p>T$, so neither bump tests that vanishing assertion in its smaller support range.

**Consequence for the geometric bridge.** If $p>T$, the norms on the entire $U_p\pi^\mathbb Z$ orbit are outside $(T^{-1},T)$ except for norm one. The corrected comb therefore vanishes for two-sided tests supported in that range and vanishing at norm one. The fixed-character formula also vanishes: Its only possible log sample is $0$, where the angular integral is zero. Thus the angular and half-twist corrections do not obstruct that scalar vanishing. They also do not prove that the global $p$-piece equals the scalar. The genuine theta lifts and section cutoff above were constructed only for the trivial isotype. Identification of the Paley–Wiener operators, an admissible global kernel lift, and equality of diagonals are still separate premises.

## Checked density of real-band weighted theta levels

**Scope:** The rational real-lattice model, with the even generators
$b\in\mathcal S(\mathbb R,\mathbb C)$ and $b(0)=\widehat b(0)=0$.
No assertion about auxiliary-place transitions or about equality of the
full adelic and real-lattice closures is needed for the Lean result.

The digest-matched text of Proposition 7.3.2.2(1), pp. 352–353, uses
compactly supported frequency profiles plus two corrections to obtain
sequential density. Equations (7.3.2.14)–(7.3.2.15), p. 355, specify the
invariant band and two-mode restrictions; (7.3.2.18)–(7.3.2.20), pp. 355–356,
assert nesting, density, and the inclusion from absolute levels. With
$S'=S=\{\infty\}$ there is no auxiliary-place choice. The standard global
lift here is $b\otimes\mathbf1_{\widehat{\mathbb Z}}$, not the sum over
local real norm-one units. The band condition is on additive Fourier
frequency before taking theta. The weighting in (11.2.1.7), pp. 488–489,
is applied before taking the Hilbert closure. These source comparisons use
layout text only, not a verified visual reading.

- [`Masullo.exists_tendsto_fourierBand_twoMoments`](../../Proofs/Props/SchwartzTwoMomentBand.lean)
  proves Schwartz convergence with exact evenness, both zero modes, and a
  positive finite band for each approximant. As in the manuscript, the
  frequency-side corrections kill evaluation and total mass. The Lean
  specialization takes the even part of the corrected profiles, which
  preserves both corrections and compact support, then inverts Fourier.
- [`Masullo.continuous_rationalThetaWeightedLog`](../../Proofs/Theorems/RationalThetaBandClosure.lean)
  proves continuity on the real two-mode kernel, not just integrability of
  its elements. Linearity and the existing uniform Poisson tail bound on
  bounded families give one square-integrable weighted majorant per family.
  First countability of the linear domain then gives continuity. The
  representative is $e^{\alpha|x|}(1+x^2)^{s/4}e^{ax}\theta_b(e^x)$ with
  $a\in\mathbb R$ and $\alpha,s\ge0$, hence the twist appears once.
- [`Masullo.rationalThetaWeightedLog_band_closure`](../../Proofs/Theorems/RationalThetaBandClosure.lean)
  identifies the closure of these weighted band images with that of all
  weighted even two-mode images in $L^2(dx)$. Cofinal increasing bands give
  the same union since the predicates are nested. This is density, not an
  estimate on a moving cutoff, nor a Lean theorem about projections or
  trace norms.

**Review:** `band-statement-review` (`pprJMuc`) reviewed the approximation
statement and topology. `band-image-interface` (`OCydxfl`) checked the exact
weight, twist, domain, closure statements, and Mathlib continuity route
against the accepted prerequisites. `weighted-level-review` (`AZjIddc`)
checked the source-side band, global lift, and ordering with $S'=S$.

**Checked strong limit:**
[`Masullo.tendsto_rationalThetaWeightedEvenBand_projection`](../../Proofs/Theorems/RationalThetaBandClosure.lean)
takes the closure of the complex-linear image for each band's even two-mode
tests. For any nondecreasing cofinal sequence of band radii, the orthogonal
projections converge pointwise in norm to the projector onto the full even
two-mode closure in the same weighted chart. Cofinality and the preceding
closure theorem identify the closure of the supremum; Mathlib's
`Submodule.starProjection_tendsto_closure_iSup` supplies the limiting
argument. This proves the strong limit modeled on (11.2.1.8)–(11.2.1.9),
not a nuclear limit to the same right-factor-free operator in the ambient
space. The [order comparison](trace-hardy-diagonal-q.md#removing-the-order-defect-in-the-weighted-rational-isotype)
records the repaired order, the position limit on common widths, and the
unmet geometric comparison. No coupled-cutoff estimate follows from this
Lean result.

## A zero-line descent obstruction for the ring-transition projector

**Source interface (provisional).** Equations (11.2.1.7)–(11.2.1.8), pp. 488–489, take a global weighted Hilbert closure and its **orthogonal** projector. No separate definition of the global $PW^{\mathrm{inv}}_{S,Y}$ was located in the extraction. Theorem 11.2.1.4 invokes the Chapter 7 levels via (7.3.2.20), and Proposition 7.3.2.4(2), p. 356, passes to global theta functions by tensoring outside $S'$. Take $S'=S=\{\infty\}$ in (7.3.2.12)–(7.3.2.17), pp. 354–355, with global extension by $\mathbf1_{\widehat{\mathbb Z}}$ from (2.1.4.2)–(2.1.4.5), p. 71. Enlarging $S'$ by standard integer-ring factors produces the same global generators. But the extracted (7.3.2.13) shows a unit-group indicator for extra places, at odds with the transition it cites and the self-dual factors used on pp. 356–357. The result below is for the standard transition; it does not establish that the orbital proof on pp. 495–496 uses this same range after enlarging $S'$. Chapter 7's diagram (7.3.3.1)–(7.3.3.2), p. 358, is about $PV_p$ between **different** levels, not about an orthogonal projection acting on the orbital quotient.

**Project obstruction.** At $a=0$ let $W_Y$ be the level assembled by this ring transition and closed in $H_s$, $s>1$, and let $Q_Y$ be its orthogonal projector. Each generator in the trivial isotype is a theta profile of an even real test $b$ with $b(0)=\widehat b(0)=0$ and $\operatorname{supp}\widehat b\subset[-Y,Y]$. For $t=e^x<1/Y$, Poisson summation gives a zero profile: In $t^{-1}\sum_{k\ne0}\widehat b(k/t)$ no nonzero lattice point lies in the band. Thus $W_Y$ is supported on $x\ge-\log Y$. This persists under the theta-image closure (point evaluation is continuous), and under the $H_s$ closure (vanishing on a half-line is a closed condition). The norm in (9.1.2.3), pp. 399–400, is the $H_s$ norm on this isotype up to a constant from compact Haar measure, so it gives the same orthogonal projector.

Write $w_s(x)=(1+x^2)^{s/2}$ and $N=\ker P$. Since $P$ has a bounded right inverse, $N^\perp=\operatorname{ran}P^*$. With circle measure $dx$ on one period, $P^*u(x)=u([x])/w_s(x)$ by unfolding. Such a vector cannot vanish on an entire left half-line unless it is zero. In particular $W_Y\cap N^\perp=0$. If $Q_Y$ preserved $N$, self-adjointness would force $Q_YN^\perp\subset W_Y\cap N^\perp=0$, and hence $W_Y\subset N$.

In fact $W_Y\not\subset N$ for **every** $Y>0$ and every $p$. Choose $c>1$ and an even Schwartz $g$ with nonnegative, nonzero smooth Fourier transform supported strictly inside $(-Y/c,Y/c)$ and away from zero. Then $g(0)>0$, and $b(t)=g(t)-g(ct)$ is a level-$Y$ test with both moments zero. For the *unsubtracted* profile $F(x)=\sum_{k\ne0}g(ke^x)$, Poisson summation gives $F(x)=-g(0)$ for sufficiently negative $x$, and Schwartz decay gives $F(x)\to0$ as $x\to+\infty$. The theta profile of $b$ is $F(x)-F(x+\log c)$, of integral $-g(0)\log c\ne0$ by integrating the difference over $[-R,R]$ and shifting the endpoints. This is also the integral of its periodization. Therefore $P Q_Y|_N\ne0$: Equal quotient classes need not give equal projected classes. The failure occurs already for genuine theta lifts, since $D$ of the theta image is dense in $N$ and $P Q_Y$ is bounded. This tests descent in the repaired zero-line Hilbert quotient, not the ambient trace convergence of Theorem 11.2.1.4, nor the $a=1/2$ operator in Theorem 11.3.2.1.

**Why the transition matters.** On the literal nonempty auxiliary-unit reading of (7.3.2.13), a finite set $T$ of extra primes replaces the raw theta profile $F_b(x)$ by $\prod_{q\in T}(1-\mathrm{shift}_{\log q})F_b(x)$, where $\mathrm{shift}_d f(x)=f(x+d)$. The adelic vanishing at $0$ then does not imply $b(0)=0$. The integral-zero condition still gives an eventually constant left tail $-b(0)$ for $F_b$, so each fixed $T$ gives a half-line support bound $x\ge-\log(Y\prod_{q\in T} q)$. But nontrivial periodization of the level is no longer automatic: For fixed $T$ containing $p$ and another prime, applying the other difference first makes the profile an $H_s$ vector; the $p$ difference then puts the resulting level in $N$. Its projector descends as zero in that reading. Conversely, the closed span over *all* auxiliary sets on the literal unit reading, including the empty set, would be all of $H_s$ at each $Y$: Given an even two-moment test $b$ of any finite Fourier band, choose a large prime $q$ so $g(t)=b(t/q)$ has band inside $[-Y,Y]$. Subtract the $T=\{q\}$ profile of $g$ from its $T=\varnothing$ profile to recover $F_g(x+\log q)=F_b(x)$. Such bandlimited profiles are dense by the approximation below. Neither alternative is the level from the standard transition; the choice matters for descent.

**Comparison on specified lifts.** The levels increase with $Y$ and their union is dense in $H_s$. Indeed, on even moment-zero real tests truncate the additive Fourier transform with smooth even cutoffs equal to one near zero, and subtract a multiple of a fixed even smooth bump off zero of integral one to restore zero integral of the transform. The approximation is in Schwartz topology, and theta summation into $H_s$ is continuous there on the two-moment subspace by the Poisson bounds above. Combine this with density of the theta image. Hence $Q_Y\to1$ strongly. Use the fixed genuine lifts $v_n$ above and put $T_{\rho,Y}e_n=\lambda_n P(\rho Q_Yv_n)$, with convolution applied on the circle **before** lifting. For any $0\le\rho\le1$,

$$\|T_{\rho,Y}-T_\rho\|_1\le\|P\|\sum_n |\lambda_n|\,\|(Q_Y-1)v_n\|_{H_s}\longrightarrow0.$$

The majorant is summable by the polynomial lift bounds and rapid multiplier decay. The convergence is uniform over the position profiles, so along any joint limit $Y\to\infty$, $\rho\to1$ pointwise, these traces converge to the circle trace. This estimate uses the specified lifts at finite cutoff and works for either twist in $\lambda_n$; the **projector** is still the one at $a=0$. This does not give a joint limit in the manuscript order.

**The manuscript order at fixed position cutoff.** Equation (11.2.1.9), p. 489, places $Q_Y$ before convolution and multiplication by $\rho$; the extra geometric projection in (10.4.1.6), p. 457, is the identity on this dense zero-line theta isotype. For this order choose a bounded section with specified genuine lifts of the individual modes. Start with the bounded bump section $J_0u=w(x)u([x])$. Correct each $v_n$ by an element of $D$ of the theta image to get $v'_n$ satisfying $\|v'_n-J_0e_n\|_{H_s}\le 2^{-|n|}$; this is possible since the difference has zero periodization. The map $Je_n=v'_n$ extends to a bounded section since the rank-one expansion of $J-J_0$ is absolutely trace-norm summable. Only the individual $v'_n$ are claimed to be genuine theta lifts.

Fix a smooth compactly supported $\rho$. Let $A$ be convolution on $H_s$ with the smooth compact log kernel $h_\varphi(u)e^{-au}$, and write $B_\rho=P M_\rho A$. It is trace class from $H_s$ to the circle: Convolution and compactly supported multiplication bound every output derivative on the support of $\rho$ in terms of the input $H_s$ norm. After periodization this bounds the map into ordinary circle Sobolev $H^m$, whose inclusion into $L^2$ has summable singular values for $m>1$. Consequently

$$\|B_\rho Q_YJ-B_\rho J\|_1\le\|J\|\,\|B_\rho(Q_Y-1)\|_1\longrightarrow0,$$

by finite-rank approximation of $B_\rho$ and strong convergence of the self-adjoint $Q_Y$. To then remove $\rho$, note that $A J$ is trace class into $H_s$: The $A(J-J_0)$ part follows from the section correction, and for $A J_0 e_n$ integration by parts in the log convolution variable gives rapid decay in $|n|$ uniformly on its fixed compact output support. Thus $P M_\rho A J\to P A J=A_{\mathrm{circle}}$ in trace norm for $0\le\rho\le1$ tending pointwise to one. This proves an **iterated**, lift-based comparison in the original composition order at $a=0$ (untwisted convolution), also allowing a twist of the convolution without changing the zero-line projector. It supplies neither a joint estimate in that order nor the weighted projector at $a=1/2$ or an identification with the partitioned global diagonal in (11.3.2.3)–(11.3.2.5), pp. 495–496.

**Review status:** Independent Yah review checked the source interfaces against the pinned extraction and verified non-descent and both trace-norm arguments for the ring-transition level. Neither this review nor the comparison checked the manuscript visually or elaborated Lean. The [half-weight comparison below](#half-weight-untwisting-and-the-iterated-limit-on-a-section) treats $a=1/2$ without assuming that the zero-line density argument applies to the weighted closure.

## Half-weight untwisting and the iterated limit on a section

**Source interface (provisional).** The weighted geometric space in (10.1.1.3), p. 434, is the closure of the theta image multiplied by $|\cdot|^a$. Equations (11.2.1.7)–(11.2.1.9), pp. 488–489, similarly weight the invariant level before taking its closure and place its orthogonal projector before convolution. By (10.4.1.6)–(10.4.1.7), p. 457, the geometric projection follows convolution, then the position multiplier is applied. The orbital quotient in (11.2.2.1), p. 489, is on the zero line, whereas Theorem 11.3.2.1 fixes $a=1/2$ and (11.3.2.5), p. 496, contains a half twist. The untwisting and section below are project constructions linking these two weights in the rational trivial isotype with $I=\{0\}$ and $s>1$. This is the same integer-ring level model as above, not a resolution of the auxiliary-unit reading or an interpretation of the global indentation (11.3.2.2).

Let $T_af(x)=e^{ax}f(x)$ for $a=1/2$. Let $G_a$ be the orthogonal projector in $H_s$ onto the closure of $T_a$ of the theta image, and $Q_{Y,a}$ the orthogonal projector onto the closure of $T_a$ of the ring-transition level. Let $A$ be ambient convolution by $h_\varphi$ and $A_a$ convolution by $h_a(u)=e^{-au}h_\varphi(u)$. Both operators are bounded on $H_s$ by polynomial translation bounds and compact kernel support. On genuine theta lifts $T_{-a}AT_a=A_a$ by substitution, including the minus sign. The range of $G_a$ is translation invariant and hence $A$-invariant, so $G_a A Q_{Y,a}=A Q_{Y,a}$.

**The cutoff is essential for boundedness.** For bounded $\rho$ supported on a compact log interval, $R_{\rho,a}=P M_\rho T_{-a}$ is a bounded map from ambient $H_s$ to the circle: Treat the two multipliers as a single multiplication, obtaining

$$\|R_{\rho,a}\|\le \|P\|\,\|\rho e^{-ax}\|_\infty.$$

There is no bounded uncut extension, even from the weighted geometric space and even when tested only on genuine theta inputs. Write $S_df(x)=f(x+d)$. For any genuine lift $f$ of $e_0$ and $d\in L\mathbb N$, $S_df$ is a genuine lift of the same mode. But

$$\|T_a S_df\|_{H_s}= e^{-ad}\|S_dT_af\|_{H_s}\le C_s e^{-ad}(1+d)^{s/2}\|T_af\|_{H_s}\longrightarrow0,$$

while $P T_{-a}T_a S_df=e_0$. The uncut map on weighted theta inputs is therefore not even closable. In particular no uniform bound on $R_{\rho,a}$ over position cutoffs exhausting the line follows from restricting the inputs to weighted theta: For each such lift, $P(\rho S_df)$ converges to $e_0$ as $0\le\rho\le1$ tends pointwise to one. This does not rule out uniform estimates on a particular smoothed sequence of level errors.

**Level limit at fixed position support.** One has $Q_{Y,a}\to G_a$ strongly. For an even real Schwartz test $b$ with the two moments zero, truncate its Fourier transform by smooth even cutoffs tending to one, equal to one near zero, and subtract a multiple of a fixed even smooth unit-integral bump supported off zero to restore $b(0)=0$. For large $Y$ both terms lie in the band $[-Y,Y]$, and the tests converge in Schwartz topology. The map $b\mapsto T_a\Theta_{2b\circ\exp}$ is continuous on this two-moment subspace into $H_s$: For $t=e^x\le1$, Poisson summation and two integrations by parts bound the unweighted theta sum by $C t\|b''\|_1$; for $t\ge1$ the original sum is $O(t^{-N})$ for each $N>1$, with a bound from a Schwartz seminorm. Multiplication by $t^a$ is harmless in both estimates on choosing $N>a+1$. The rational finite-ball reduction above covers every trivial-isotype theta profile. Thus the increasing weighted levels have dense union in $\operatorname{ran}G_a$, not by a zero-free-line argument and without claiming density in all of $H_s$.

For a specified section, use the genuine lifts $v_n$ above. Their log profiles vanish above a common upper bound, since all $B_n$ have support in a fixed compact set and $\log k\ge0$ in the theta sum. Therefore $\|T_av_n\|_{H_s}$ grows at most polynomially. Choose $d_n\in L\mathbb N$ by rounding $C\log(2+|n|)$ up to a multiple of $L$, with $C$ large enough that the translation bound gives $\sum_n\|T_a S_{d_n}v_n\|_{H_s}<\infty$. Define $J_a e_n=T_a S_{d_n}v_n$. This extends by the absolutely summable rank-one series to a trace-class map from the Hilbert circle into $\operatorname{ran}G_a$. It specifies genuine weighted theta lifts of each mode and a right inverse to untwisted periodization on finite Fourier sums, not a section of a bounded quotient map on the weighted closure.

Then the circle operators $R_{\rho,a} A Q_{Y,a}J_a$ converge in trace norm at each fixed $\rho$ to $R_{\rho,a} A J_a$. Indeed $\|(Q_{Y,a}-G_a)J_a\|_1\to0$ by the summable mode bounds and strong convergence. This uses the level, convolution, and position cutoff in the order of (11.2.1.9), with the geometric projection redundant on the indicated range.

**Removing position support after the level limit.** The image of each mode after convolution and untwisting is $S_{d_n}A_av_n$. These vectors are summable in $H_s$, for a reason not implied by the weighted input bound. With $B_n=w e_n-c_n Dq$ as above, let $C_n=h_a*B_n$. The supports of $C_n$ lie in one fixed compact interval, and their exponential moments vanish since $\int e^x C_n(x)\,dx=(\int e^u h_a(u)\,du)(\int e^xB_n(x)\,dx)$. Each fixed smooth seminorm of $C_n$ is rapidly decreasing in $|n|$: In the convolution with $w e_n$ integrate by parts in the variable carrying $e_n$, and $c_n$ is rapidly decreasing by the same argument against $e^xw(x)$. Theta summation commutes with log convolution here (at a fixed $x$ the compact supports bound the contributing $k$), so $A_av_n=\Theta_{C_n}/\zeta(i\omega_n)$. The preceding Poisson and Schwartz bounds now give rapid decay of $\|A_av_n\|_{H_s}$, even after the polynomial factor from $1/\zeta(i\omega_n)$. The shifts $d_n=O(\log(2+|n|))$ preserve summability by the polynomial translation bound.

It follows by termwise dominated convergence in the trace norm that $R_{\rho,a} A J_a\to A_{\mathrm{circle}}$ as $0\le\rho\le1$ tends pointwise to one. In fact $P A_a S_{d_n}v_n=\lambda_n e_n$: Periodization interchanges convolution with circle convolution, and $P S_{d_n}v_n=e_n$. The trace is the half-twisted comb computed above. This is an **iterated** limit in the ring-transition model on the indicated lifts, not a finite-level descent statement or a comparison with the partitioned global diagonal.

**Review and next step:** Independent Yah review checked the estimates and the source interfaces against the digest-matched extraction. No visual or Lean check was performed. Next, use the half-line support of the level and quantitative Fourier-band approximation of the shifted tests to see whether the trace-norm level error can absorb the growing untwisting norm and yield a joint estimate.

## A coupled level and position limit at half weight

**Scope and source interface.** Use the same rational trivial isotype, $s>1$, $a=1/2$, and the standard integer-ring transition. This is a project estimate on specified lifts in the order of (11.2.1.9), p. 489. The digest-matched layout extraction of Definition 9.3.3.1, p. 427, puts the position cutoff in $[\Lambda^{-1},\Lambda]$ in norm, so its log support lies in $[-\log\Lambda,\log\Lambda]$. The proof after (11.3.2.4), p. 496, invokes a sufficiently large level and $\varepsilon\Lambda=o(1)$ but the extracted sentence gives no quantitative rate relating the level to $\Lambda$. The condition below is sufficient for our model, not a reading of that sentence or an identification of its diagonal.

**A trace-norm rate for the projected lifts.** Keep the previous section $J_a$, choosing the constant in $d_n=O(\log(2+|n|))$ large enough that

$$\|J_a e_n\|_{H_s}\le C(2+|n|)^{-2}.$$

This follows from the exponential factor $e^{-ad_n}$ in the weighted translation bound. Let $b^{(n)}(y)=b_{n,\infty}(e^{d_n}y)/\zeta(i\omega_n)$, so $J_a e_n$ is its weighted theta sum. For each fixed Schwartz seminorm, the seminorm of $b^{(n)}$ grows at most polynomially in $2+|n|$. The unshifted test has fixed compact support off zero and polynomial derivative bounds, the inverse zeta factor has polynomial growth, and each derivative of the dilation costs a fixed power of $e^{d_n}$.

For an even two-moment Schwartz test $b$, define $b_Y$ in Fourier coordinates, for sufficiently large $Y$, by

$$\widehat b_Y(\xi)=\psi(\xi/Y)\widehat b(\xi)
-\gamma(\xi)\int_{\mathbb R}\psi(\eta/Y)\widehat b(\eta)\,d\eta.$$

Here $\psi$ is even and smooth, supported in $[-1,1]$ and equal to one on $[-1/2,1/2]$. The fixed $\gamma$ is smooth, even, supported off zero inside $(-1,1)$, and of integral one. Thus $b_Y$ has both moments zero and belongs to the real band $Y$. For each fixed Schwartz seminorm $q$ there is a finite Schwartz seminorm bound $q'$ with $q(b-b_Y)\le C_qY^{-1}q'(b)$. Indeed the Fourier remainder $(1-\psi(\xi/Y))\widehat b$ and all its terms after differentiation are supported in $|\xi|\ge Y/2$ and bounded by Schwartz seminorms there; one extra weight gives the factor $Y^{-1}$. For the scalar correction use $\int\widehat b=0$ to write its coefficient as minus the integral of that same tail, using an integrable weight as well. The Fourier transform and its inverse preserve the Schwartz topology.

Apply the weighted theta continuity estimate from the previous section to $b^{(n)}-b_Y^{(n)}$. Since the projector is the best approximation in $H_s$, the band approximation and the bound by the norm of the input give, for some fixed $M\ge0$,

$$\|(Q_{Y,a}-G_a)J_a e_n\|_{H_s}
\le C\min\{(2+|n|)^{-2},\ Y^{-1}(2+|n|)^M\}.$$

In the rank-one expansion of $(Q_{Y,a}-G_a)J_a$ sum the second bound for $|n|\le H$ and the first for $|n|>H$. For $H\asymp Y^{1/(M+2)}$ this proves

$$\|(Q_{Y,a}-G_a)J_a\|_1\ll Y^{-1}H^{M+1}+H^{-1}\ll Y^{-\beta},\qquad \beta=1/(M+2)>0.$$

**Joint convergence on an explicit family of paths.** For $0\le\rho\le1$ supported on a compact log interval with lower endpoint $-R$, the level error after convolution and untwisting is bounded in trace norm by $C e^{aR}Y^{-\beta}$. The position error after the level limit tends to zero in trace norm for any such profiles tending pointwise to one, by the summable smoothed outputs in the previous section. Hence the operators $R_{\rho,a} A Q_{Y,a}J_a$ converge in trace norm to the half-twisted circle convolution along every joint path with $\rho\to1$ pointwise and $e^{aR}Y^{-\beta}\to0$. In particular, for the log support $[-\log\Lambda,\log\Lambda]$, one may take $Y\ge\Lambda^q$ for any fixed $q>a/\beta$ with this section. This is a rate condition, not merely a diagonal-sequence argument based on the fixed-position convergence.

**What the half-line support adds.** If the kernel of $A$ is supported in $[\ell,u]$, then $A Q_{Y,a}$ has outputs supported in $x\ge-\log Y+\ell$. On this region the untwisting factor is at most $e^{-a\ell}Y^a$, regardless of the position cutoff. Below it the level error after untwisting is just the omitted part of $T_{-a}AJ_a$ with a minus sign, whose trace norm tends to zero there by the same summable untwisted outputs. For any fixed *finite* set of circle modes the band argument gives $O(Y^{-K})$ at every $K$ (use $K$ extra weights instead of one), so on that finite subspace no position-to-level rate condition is needed. For the full trace-norm comparison the summed rate above need not beat $Y^a$; modewise rapid convergence does not provide the summable estimate uniform in $Y$ required by that argument. No unrestricted joint limit or equality with the partitioned global diagonal follows. The non-descent and auxiliary-unit issues remain unchanged.

**Review status:** Independent Yah review checked the rate, the finite-mode support argument, and the digest-matched extraction at the cited locators. No visual review or Lean check was performed.

## The right cutoff erases a fixed shell in the literal chain

**Provisional source reading.** In (11.3.1.2), pp. 492–493, the indicators $\alpha_k$ require units at the growing set $P_k$. Equation (11.3.1.4), p. 494, uses the signed difference $\alpha_{k+1}-\alpha_k$. For a fixed shell $k$, (11.3.2.3), p. 495, appears to multiply this difference by $\alpha_{k_1}$ in the same input variable $y=\xi g\tau(t)$. The text leading to (11.3.2.4), pp. 495–496, then treats the limit of $\alpha_{k_1}$ as $\beta_{S'}$, the requirement of units *outside* $S'$, where $S'$ contains the places newly added in the chosen shell. We do not see a separately indexed exhaustion in that passage. If the input factor is the same chain, there is an exact obstruction, independent of the indentation, position cutoff, and band level:

$$(\alpha_{k+1}-\alpha_k)\alpha_{k_1}=0\qquad(k_1\ge k+1).$$

Indeed $\alpha_{k_1}=1$ implies both earlier indicators are one, and otherwise the product is zero. This holds even if the input is already supported in the $k$th stratum. In contrast, $\beta_{S'}$ permits a nonunit in $P_{k+1}\setminus P_k$. The cited carving theorem does index its sets outside a base $S$, by (11.1.2.1), p. 480. Rebasing that exhaustion at $S'$ is a possible repair, not an explicit identification of the chain in the extracted passage. Use finite sets exhausting the places **outside $S'$**, with no unit constraint added inside $S'$, to obtain $\beta_{S'}$ pointwise. This repairs that limit of multipliers, not the orbital trace identity. The shell condition alone does not imply support in the $S'$-idele subgroup: Over $\mathbb Q$, multiplying the diagonal rational $p$ by any sufficiently late prime outside $S'$ still gives an idele in the same $p$-shell. The reading of the indices and the indentation (11.3.2.2) still need rendered-page verification.

**Conditional Haar lift in the rational trivial isotype.** Let $G=\mathbb A_{\mathbb Q}^\times$, $H=\mathbb Q^\times$, and choose the positive real section with finite coordinates one. Then $D=\mathbb R_{>0}\times\widehat{\mathbb Z}^{\times}$ is a clopen fundamental subgroup: Clearing all finite valuations and then choosing the real sign gives $G=H D$ and $H\cap D=\{1\}$. Write $\sigma(q)\in D$ for the representative of $q\in G/H$. In this splitting the norm-one part of $D$ is $E_{\mathbb Q}^1$ from (A.2.3.14), p. 549. Use counting measure on $H$ and quotient Haar $\mu$. Since $G$ is the disjoint union of its open translates $hD$, Haar integration is the sum over $h$ followed by integration over $D$ with the restriction of Haar on $G$. That restriction pushes forward to $\mu$ by the quotient Haar formula. This directly gives the unfolding used in (12.2.2.4)–(12.2.2.7), p. 508, without invoking the connected fundamental domain hypothesis on p. 507: $D$ is not connected.

Fix a finite probability vector $(m_j)_{j\in\mathbb Z}$. Define $u_0(p^j d)=m_j$ for $d\in D$, where $p^j$ is a diagonal rational, and take $u_0=0$ on other translates of $D$. This is continuous, nonnegative, supported properly over the quotient (finitely many copies of any compact set of classes), and has orbit sum one. It is an indentation in the sense of (12.2.1.2) and Definition 12.2.1.3, pp. 505–506, rather than an indicator of the thin norm section. Let $u_0^\Delta$ be the diagonal average (12.2.2.1). At $x=\sigma(q)$, $y=h\sigma(r)$ it vanishes unless $h=p^\ell$, in which case it equals $\sum_j m_j m_{j+\ell}$. Thus summing over *all* input translates recovers the original kernel $K(q,r)$ from the lift $u_0^\Delta(x,y)K([x],[y])$.

Consider the step adding $p$ and choose $S'$ to contain it. All nonzero lifted weights at $x\in D$ have $y$ unit outside $p$, so the exhausting cutoffs outside $S'$ and their limit $\beta_{S'}$ all equal one on this support. The positive shell indicator $\alpha_k-\alpha_{k+1}$ then selects exactly $\ell\ne0$. Its input orbit sum gives the operator kernel $cK(q,r)$ with

$$c=\sum_{\ell\ne0}\sum_j m_j m_{j+\ell}=1-\sum_j m_j^2.$$

The manuscript sign $\alpha_{k+1}-\alpha_k$ gives $-cK$. Any bounded norm-only input cutoff $b$ passes through the orbit sum, since a principal idele has norm one. With position multiplier $\rho$ the descended signed kernel is therefore $-c\rho(q)K(q,r)b(|r|_{\mathbb Q})$. This statement is about lifting a given kernel; a norm-only input multiplier is not identified with the orthogonal level projector (11.2.1.8), p. 489.

If $K$ is invariant under norm-one translations separately in both variables and has a compatible regular Haar diagonal $d(q)$ (or one uses its biangularly invariant regularization), the signed shell integral in the repaired lift is consequently

$$-c\int_{C_{\mathbb Q}} \rho(q)b(|q|_{\mathbb Q})d(q)\,d\mu(q),$$

whenever the integral is absolutely convergent. For a sharp radial threshold, its one boundary norm has Haar measure zero, and the multiplier is locally constant away from it. The first point in (11.3.2.3) is $\tau(t)$, not $g\tau(t)$; the second has class $[g\tau(t)]$. Replacing the first by $g\tau(t)$ to use the Haar diagonal here relies on radiality in the first variable and on the angular independence of our lift weights. It is not a diagonal argument for the full kernel without isotype reduction.

**What this does not identify.** The same kernel and full diagonal give different shell integrals for a point mass ($c=0$) and two equal masses ($c=1/2$), if the cutoff diagonal integral is nonzero. More directly, the point-mass indentation always gives zero in this shell, whereas the section-based half-twisted circle trace is nonzero for a radial nonnegative test supported close to log norm $\log p$ with positive value there. Thus admissibility and preservation of the full diagonal alone cannot imply the orbital trace comparison. An independent identification of the selected shell operator with the orbital quotient is still needed. Neither the unrestricted joint limit nor the precise source level identification was changed here.

**Review status:** Independent Yah review checked the cutoff calculation, the rational lift and its Haar unfolding, and the source interfaces against the digest-matched extraction. No visual or Lean check was performed.

## Main cutoff test: No Haar lift of the literal shell kernel

**Scope and outcome:** Over $\mathbb Q$, for the trivial compact isotype,
$S=\{\infty\}$, $a=1/2$, one common admissible $0<\alpha<1/2$, and even
$s\ge4$, the first failure is the lift **from the quotient geometric
kernel on $C_{\mathbb Q}^2$ to a Haar-compatible idele kernel on
$(\mathbb A_{\mathbb Q}^{\times})^2$**. This happens with cutoffs fixed,
before either of the two limits in the positive-log control. The source
reading is provisional: Pinned Markdown and digest-matched numbered
layout extraction agree on the two simultaneous indicators and the same
right-cutoff index family, but the page render was not inspected.

**Unsplit source operator and measures.** Write $G=\mathbb A_{\mathbb Q}^\times$,
$H=\mathbb Q^\times$, $C=G/H$, and $K=\widehat{\mathbb Z}^{\times}$.
Use the positive real section $\tau$ with all finite components $1$ and
$D=\tau(\mathbb R_{>0})K$, the rational fundamental subgroup from
(A.2.3.14), p. 549. On $C$ use $d\bar\mu=dk\,dx$ with $x=\log|g|$ and
$dk(K)=1$ by (A.3.2.1), pp. 559–560. The corresponding Haar on $G$ uses
counting measure on $H$ and the same measure on each translate of $D$.
The Hilbert measure on the radial isotype is $w(x)\,dx$ with
$w(x)=e^{2\alpha|x|}(1+x^2)^{s/2}$ by (9.2.2.34), p. 417. The raw kernel
(10.4.3.50), pp. 473–474, uses input Haar $d\bar\mu$, not the weighted
Hilbert measure. In the order of (10.4.1.12), p. 458, the unsplit compact
position truncation is $M_\rho A(\varphi)P$, with $P$ the half-twisted global
geometric orthogonal projection. The carving in (11.3.1.4), p. 494, is
not yet an operator on this quotient: The unit indicators distinguish
representatives of the same class (for instance $1$ and the diagonal
prime added at this step).

At the stated domain of (11.2.1.8–9), pp. 488–489, the global level
composition is $M_\rho P A(\varphi)Q_B$, where $Q_B$ is the global invariant
level projection on the right. The printed statement uses the polynomial
$W^{s,2}$ norm; a positive-width $Q_B$ must be constructed in the same
weighted chart as $P$, not identified by transporting that projection.
In the [common weighted model](trace-hardy-diagonal-q.md#the-fixed-cutoff-limit-retains-a-right-projection),
$Q_B\to P$ strongly gives the level-first compact-position limit
$M_\rho P A(\varphi)P=M_\rho A(\varphi)P$, not $M_\rho P A(\varphi)$.
The equality uses invariance of the geometric range, not commutation.
The local projected convolution in
[`fixedAnnulus_trace`](../../Proofs/Theorems/RationalFixedAnnulusTrace.lean)
is instead on the weighted real log line with the **local** two-moment
band projector on the right and log Lebesgue measure in the kernel.
The additive Fourier-multiplier operator of (12.4.1.8–12), p. 517,
uses the additive measure in its kernel; it is not either projection.

**The first missing map.** For a Haar-relative quotient kernel $k$ of
the unsplit operator, a lift $Lk$ that recovers its integral action on
quotient inputs must satisfy the row identity, before shelling,

$$
\sum_{h\in H}(Lk)(x_0,hy_0)=k([x_0],[y_0]),\qquad x_0,y_0\in D,
$$

in the relevant almost-everywhere kernel sense (after angular averaging
if working only with radial inputs). This follows by disintegrating the
input Haar integral on $G$ over its countable translates of $D$.
Proposition 12.2.2.2, (12.2.2.1–7), pp. 507–508, supplies such an orbit
normalization for the two-leg weight of an actual $H$-indentation and
unfolds the regular Haar diagonal. Indeed the sum of its two-leg weight
in the input row is $1$: Sum over the input translates first, using the
indentation normalization, then over the translates in the remaining
output leg. Bare pullback is constant on the input rational orbit and
has no such normalization. The proposition's diagonal uses $(x_0,hx_0)$
with $x_0=g\tau(t)$; the display in (11.3.2.3) uses $(\tau(t),hg\tau(t))$.
Radiality removes $g$ from the first argument of the quotient kernel,
not from an arbitrary lifted weight. The proposition neither identifies
an orbital lift nor licenses the claimed nuclear extension from
$\mathcal S(\mathbb A_{\mathbb Q})$ to an endomorphism of $W_I^s(C)$.

In (11.3.2.2), p. 495, the extraction leaves the inner differential
implicit. Use the $d\mu_1(g)$ Haar of the surrounding displays. For each
$\xi\in H$ and each first input $x_0\in G$, the condition
$\xi g x_0\in\tau(\mathbb R_{>0})$ allows at most one $g\in K$:
Two such choices would differ by an element in
$K\cap\tau(\mathbb R_{>0})=\{1\}$. The Haar measure of that singleton is
zero because $K$ is infinite. Every summand in (11.3.2.2) is therefore
zero. As a multiplicative Haar weight it has row mass zero, not one,
and would take every quotient kernel to zero. Even before integration,
both indicators at $(\tau(t),\xi g\tau(t))$ can be nonzero only if
$\xi g=1$: The ratio of the arguments is in the norm section and has norm
one. Thus merely assigning mass to the exact section without changing the
simultaneous support condition could not give any nonempty prime shell.

**The next cutoff on the same reading.** In (11.3.2.3), p. 495, the right
factor $\alpha_{k_1}(y)$ independently annihilates
$(\alpha_{k+1}-\alpha_k)(y)$ pointwise for $k_1\ge k+1$. For the prime $p$
added in shell $k$, $y=p\tau(t)$ (diagonal $p$) has shell factor $-1$ and
$\beta_{S'}(y)=1$ with $S'=\{\infty,p\}$, but $\alpha_{k_1}(y)=0$ for all
those $k_1$. Restricting to the shell therefore does not produce the
claimed limiting cutoff in (11.3.2.4), pp. 495–496. Neither this factor
nor the $S'$-rebased replacement is a right Hilbert projection. The
[normalized collar](trace-section-collar-q.md#the-fixed-cutoff-base-operator-and-its-shell-masks)
and other admissible lifts do not identify the source operator; valid
lifts can put different mass in the shell of the same quotient kernel.

**Disposition:** The literal zero integral is not the orbital term of
an identified global trace decomposition. The short bump was not used
to claim a match, discrepancy, or orbital vanishing for a valid lift.
Do not rerun the [positive-log control](trace-to-zeros.md#first-unmatched-geometric-evaluation-and-a-positive-log-control)
until there is a specified Haar-compatible lift of this quotient kernel,
a right cutoff that preserves the intended shell, and a comparison of
the resulting shell operators with the orbital quotients on compatible
levels. Take the global level limit before position exhaustion if that
comparison becomes available. No zero-location conclusion follows.

**Independent review:** Yah session `01a20423-6e7a-7d64-a52b-fd38fb5c5973`,
child `source-review` (`eorRcBP`), checked the Haar unfolding, null
section, same-chain cutoff, and alternative readings against the pinned
text. The mathematical deductions are conditional only on the stated
literal readings. Neither reader verified the renders; no Lean proof
was added or re-audited for this source check.

## Half-twisted reflection of the rational theta projector

**Source interface (text extraction).** Theorem 2.2.3.2, p. 82,
gives $\Theta_b(t)=t^{-1}\Theta_{\widehat b}(t^{-1})+
 t^{-1}\widehat b(0)-b(0)$ in the rational unramified model. The two
corrections vanish on the source of the weighted theta profiles in
(11.2.1.7), p. 488. The weighted level projectors and level-first
cutoff composition are (11.2.1.8)–(10), p. 489. Theorems 11.2.1.2
and 11.2.1.4 require tests supported at norms at least one. Theorem
11.3.2.1, p. 495, requires support strictly above one. Its invocation
on p. 520 is for the tests of Theorem 12.5.1.1, p. 519, which may
live on both sides and need only vanish on the norm-one fibre.
Finite-place sample vanishing does not extend the orbital theorem.

**Project repair in Lean.** In the rational even two-mode lattice
model, `rationalThetaLogReflection` is the complex-linear isometric
involution $Ru(x)=u(-x)$ on the unweighted log-line $L^2$ chart.
[`rationalThetaLogReflection_weightedLog`](../../Proofs/Theorems/RationalThetaReflection.lean)
uses the checked inversion, the even weight root $W$, and the half
twist to show
$W(-x)e^{-x/2}\Theta_b(e^{-x})=W(x)e^{x/2}\Theta_{\widehat b}(e^x)$.
Fourier exchanges the zero modes and squares to the identity on the
even input. `rationalThetaLogReflection_freq_image` consequently
maps the closed theta image with Fourier support in a set to the
closed theta image with **spatial** support in that set. This is not
covariance of the same finite Fourier-band projector. With the
constraint removed, `rationalThetaLogReflection_starProjection`
proves $RG=GR$ for the full geometric orthogonal projection $G$.

**Use at fixed position cutoff (reviewed mathematics, not Lean).**
In this chart $R$ conjugates a log convolution $A_F$ to $A_{\check F}$,
where $\check F(x)=F(-x)$, and commutes with the symmetric log-position
cutoff multiplier $M_\rho$ of Definition 9.3.3.1, p. 427. At compact
position support, $M_\rho A_F$ is trace class for smooth compact $F$:
Both variables lie in compact intervals, the smooth convolution
kernel extends to a smooth periodic kernel on a larger rectangle,
and the chart factors and cutoff are bounded multipliers there.
The strong cofinal level limit $Q_Y\to G$ gives the trace-norm limit
$M_\rho G A_F Q_Y\to M_\rho G A_F G$. Here convolution preserves
the full theta space, so $G A_F Q_Y=A_F Q_Y$. The terminal $G$ is
essential to the limit, as in the [operator-order audit](trace-hardy-diagonal-q.md#the-fixed-cutoff-limit-retains-a-right-projection).
Unitary conjugation of this corrected limit gives equality of the
whole fixed-position traces for $F$ and $\check F$. This reduces a
strictly below-one test to an above-one test for the total rational
level-first trace. It does not transport shell traces, change the
cutoff order, or extend by itself to tests touching norm one.

Independent Yah `reflection-review` checked the statement, signs,
operator order, and scope against the digest-matched extraction and
accepted Lean dependencies. The rendered-page check remains open.
Audit scope: `Lemmas.RationalThetaLogReflection` and
`Theorems.RationalThetaReflection`, including the pullback,
involutivity, input Fourier map, reflected generators, support swap,
and full projection equation.

**Next:** Use the [above-one control](trace-to-zeros.md#first-unmatched-geometric-evaluation-and-a-positive-log-control)
with the actual global diagonal. Independently identify an admissible
shell operator or compute its value on that control, and compare the
$S$-piece with the normalized local value minus both Mellin terms.
Neither reflection of the total trace nor the scalar explicit formula
can supply a split of that trace into the claimed pieces.
