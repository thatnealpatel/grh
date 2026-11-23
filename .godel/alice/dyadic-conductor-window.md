# A Weil window beyond the fixed-conductor moment barrier, on average

The [each-prime theorem](prime-conductor-window.md) tests all functions in a growing window for most characters of **each** prime conductor. Its proposed next test at $A=2.1$ has two quantifiers worth separating. Here the large-values estimate up to height $Q^{1.2}$ works with the same window and all the same tests, but with a density-one set of prime conductors. This does not settle the each-prime question.

## Statement

Let $Q\to\infty$, $Q\le q\le 2Q$ be prime, and $\chi$ range over the nonprincipal characters modulo $q$. Use counting measure on pairs $(q,\chi)$. For fixed $A>0$ and $0<\alpha<2$, put $b_q=\log(A\log q)$ and $\beta=1-\alpha/2$. Except for a fraction $Q^{-\beta+o(1)}$ or less of the pairs, the compact Weil floor satisfies

$$
 \lambda_\chi(b_q)\ge [\min(1,1+\alpha-A)-o(1)]\log q.
$$

The infimum is over **all** nonzero complex smooth tests compactly supported in $(-b_q,b_q)$. On the same good pairs the same lower bound holds for the whole Pick form relative to the Cauchy Gram form, for all finite sets of distinct real nodes $m\ge(\log\log q)^3$ with $\sum_m 1/m\le b_q$. The normalizations are those in the each-prime theorem. The errors are uniform in the tests, nodes, and good pairs.

In particular, $A=2.1$, $\alpha=1.2$ give a floor $(0.1-o(1))\log q$. The bad-pair fraction is at most $Q^{-2/5+o(1)}$. Apart from a fraction at most $Q^{-1/5+o(1)}$ of the primes in the dyadic interval, the bad-character fraction at a remaining prime is at most $Q^{-1/5}$. Indeed all the fibers have size $q-2\asymp Q$, so this follows by Markov's inequality. This implication cannot be reversed to cover *every* prime: Even all characters of one prime cost only $Q^{-1+o(1)}$ of the pairs.

## The extra moment length

Write $Y=Q^\alpha$, $X=(A\log Q)^2$, and fix this **common** cutoff in the moment calculation. The needed hybrid large sieve bound for any coefficients $c_n$ supported on $1\le n\le N$ is

$$
 \sum_{q,\chi}\int_{-3Y}^{3Y}\Big|\sum_n c_n\chi(n)n^{it}\Big|^2dt
 \ll (Q^2Y\log(2Q)+N)\sum_n|c_n|^2. \tag{1}
$$

Here and below the family is as in the statement. For completeness, first restrict $c_n$ to an interval of $M$ consecutive integers. Writing a primitive character by its additive Gauss sum, of modulus $\sqrt q$, and then applying character orthogonality (enlarge the sum of squares to all characters), gives

$$
 \sum_{\chi\ne\chi_0\bmod q}\Big|\sum_n c_n\chi(n)\Big|^2
 \le \frac{q-1}{q}\sum_{a=1}^{q-1}\Big|\sum_n c_n e^{2\pi i an/q}\Big|^2.
$$

The reduced fractions $a/q$ in this family are separated on the circle by at least $(4Q^2)^{-1}$. The Gram matrix of their exponential rows on the interval has diagonal $M$ and off-diagonal entries at most $1/(2\|a/q-a'/q'\|)$ in modulus, where $\|\cdot\|$ denotes distance to an integer. Summing in order of distance on each side bounds the absolute off-diagonal row sum by $O(Q^2\log(2Q))$. Thus the squared operator norm is $O(M+Q^2\log(2Q))$, independently of the interval's origin.

To incorporate time, set $\delta=1/(4Y)$ and $S_\chi(u)=\sum_{u<\log n\le u+\delta}c_n\chi(n)$. The magnitude of its Fourier transform is $|\sum_n c_n\chi(n)n^{it}|\cdot|\int_0^\delta e^{itv}dv|$ in the positive-sign convention. The second factor is $\gg\delta$ on $|t|\le3Y$. By Plancherel the left side of (1) is $\ll\delta^{-2}\int\sum_{q,\chi}|S_\chi(u)|^2du$. At each $u$ the relevant integers are in an interval of length $O(1+N\delta)$, and each $n$ belongs for a set of $u$ of length $\delta$. The interval estimate proves (1). Applying an ordinary large sieve on the full interval separately at every $t$ would instead charge $NY$, losing the gain.

Use the prime polynomial $P_\chi(t)=\sum_{p\le X}(\log p)\chi(p)p^{-1/2+it}$ and

$$
 k=\left\lfloor\frac{\log(Q^2Y)}{\log X}\right\rfloor,\qquad V=\frac{\log Q}{\log\log Q}.
$$

The coefficients of $P_\chi^k$ before twisting have squared sum at most $k!(\sum_{p\le X}(\log p)^2/p)^k$, by the multinomial formula and unique factorization; their support ends at $N=\lfloor X^k\rfloor\le Q^2Y$. There are $\asymp Q^2/\log Q$ pairs by the prime number theorem. Divide (1) by this family size. A value $|P_\chi(t)|>V$ at any $|t|\le2Y$ gives $|P_\chi|>V/2$ on an interval in $[-3Y,3Y]$ of length $\gg\min(1,V/(\sqrt X\log X))=Q^{-o(1)}$, by partial summation bounding the derivative. Consequently the fraction of pairs having such a value is at most

$$
 Y Q^{o(1)}\frac{k!\,[O((\log X)^2)]^k}{(V/2)^{2k}}
 \le Q^{\alpha-(2+\alpha)/2+o(1)}.
$$

Indeed $k\sim(2+\alpha)\log Q/(2\log\log Q)$, and the log of the ratio after $YQ^{o(1)}$ is at most $k[-\log\log Q+O(\log\log\log Q)]$. For comparison, using $qY$ instead of $Q^2Y$ in this calculation yields $q^{(\alpha-1)/2+o(1)}$ at a fixed prime, no saving at $\alpha=1.2$.

## Transferring the estimate to the two forms

For the compact tests the true cutoff is $X_q=(A\log q)^2$; for the matrices the truncation in the each-prime proof uses $X'_q=X_q\exp((\log\log q)^{-1/2})$. Uniformly $X\le X_q\le X'_q\le (1+o(1))X$. By the prime number theorem and partial summation the **unsigned** prime mass between $X$ and $\max_q X'_q$ is $o(\sqrt X)=o(\log Q)$ (subtract the two asymptotics $\sum_{p\le x}(\log p)/\sqrt p\sim2\sqrt x$). The prime powers of exponent at least two cost $O(\log X)$. Thus for every good pair either truncated prime multiplier costs $o(\log q)$ throughout $|t|\le2Y$. No maximal large sieve over variable cutoffs is needed.

Now use the frequency partition and leakage proof in the [each-prime theorem](prime-conductor-window.md), with the common $Y$. At high frequencies $\log Y=\alpha\log q+O(1)$ and the enlarged-interval Schur cost is $(A+o(1))\log q$. Neither the Schwartz tail estimate with $d=Y^{-1/2}$ nor the matrix correlation tail depends on $\alpha<1$; that restriction was used only in the fixed-modulus exceptional-set estimate. This gives the asserted uniform floors.

## Decision record

Gödel run `01a206d3-a450-7e39-a35a-dcd930c62e3b` matches Work session `01a206d3-a618-7958-b8c0-6a8a68315f63` by input and final output. Its launch marker and embedded Work prompt match `039a60eab10e0fb1db07d3b768b17fe53ceb69bb`. Audit `WPselNb` checked the compact theorem, including the domain of the Schur bound; it was not asked to review the later matrix extension. Work incorporated the newly accepted unsigned norm at `bdd74f2a`, then adopted its theorem at `85842a8f`. At improvement start (`1b943350`) that proof and the program were unchanged. Work's barrier and suggested each-prime experiment were correctly scoped; the visible work and review did not test averaging the modulus.

**Handoff decision:** Keep the each-prime target, but do not spend another cycle testing the dyadic density-one variant at $A=2.1$: The hybrid estimate above already proves it. A new fixed-modulus bound has to control the possibility that the bad pairs concentrate on individual conductors. A saving only after summing over $q$ does not do that. No change to Alice's graph or standing instructions: There was no observed recurring selection failure, and automatically relaxing a family quantifier could discard the original goal. This is a paper calculation on the handoff's parameters, not a replay of agent choices, a live program trial, a formalization, or GRH for a fixed character.
