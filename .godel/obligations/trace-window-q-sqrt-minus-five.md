# A pole test for the p. 520 window over $\mathbb Q(\sqrt{-5})$

**Result (ordinary mathematics).** Fix $0<\alpha<1/2$. With the quotient Haar measure specified in the manuscript, the two sides of (12.5.1.1)–(12.5.1.3) cannot agree on all radial tests supported above norm one over $F=\mathbb Q(\sqrt{-5})$. They disagree on translates of any nonnegative bump as below, at arbitrarily large translations. This is an obstruction to the *combined* evaluations on p. 520. It does not identify the value of either cutoff trace.

The point of translating the test is to distinguish a normalization error from the omission of zeros. Under a Laplace average in the translation parameter, the finite local sum detects the **order** of the pole of $\zeta_F$, which is one, not its residue. The positive polar moment instead detects the **volume** of $C_F^1$. Zeros in the stated window contribute to neither coefficient.

## Measure and tests

Pages refer to the [pinned edition](../sources/masullo/README.md). Source readings use layout extraction and machine reading of rendered pages, not an independent visual certification. In Theorem 12.5.1.1 the finite coefficient is $\log(q_v)/\mu_v(\mathcal O_v^\times)$, the complex coefficient is $1/(2\pi)$, and $M(\varphi)(c)=\int_{C_F}\varphi(g)c(g)\,d\bar\mu(g)$, with no volume divisor. The proof on p. 520 uses the global Haar $\bar\mu$. With counting measure on $F^\times$ and $dt/t$ on the norm quotient, (A.3.2.1), pp. 559–560, gives

$$V=\bar\mu_1(C_F^1)=\frac{2^{r_1}(2\pi)^{r_2}h_FR_F}{\sqrt{|d_F|}\,w_F}=\frac{2\pi\cdot2}{\sqrt{20}\cdot2}=\frac{\pi}{\sqrt5}\ne1.$$

Here $d_F=-20$, the units are $\{\pm1\}$, the rank-zero regulator is one, and the [class number calculation](isotypic-exhaustiveness-q-sqrt-minus-five.md#the-missing-valuations-and-the-target-character) gives $h_F=2$. Remark 9.2.0.1, p. 403, and (D.2.1.6), p. 794, distinguish this Haar from the canonical $\bar\mu/V$.

Fix a nonzero $b\ge0$ in $C_c^\infty((0,\log 2))$. Write $B(z)=\int b(u)e^{zu}\,du$. For $R\ge0$ put $\varphi_R(g)=b(\log|g|_F-R)$. This is the pullback of a smooth compactly supported function on the Lie quotient $C_F/C_F^1$ with compact kernel, so it belongs to $D(C_F)$. It vanishes on a neighborhood of $C_F^1$ and is invariant under every finite unit group. For each $R$, choose $T>2e^R$ and include in $S$ the archimedean place, the ramified places, and every place of norm $\le T$, closing under places over the same rational prime. Inverting the prime over $2$ kills the class group, so this meets the $S$ conditions on p. 520 for the trivial character. No uniform choice of $S$ is used or needed in the asserted scalar identity.

## The window has lower exponential growth than the polar term

Haar integration over the compact norm fibre kills the Mellin transform on every nontrivial compact character. On the trivial compact character it gives exactly

$$M(\varphi_R)(|\cdot|_F^z)=V e^{zR}B(z).$$

Only the trivial-character Hecke zeros survive. In the window these are the zeros $\rho$ of the finite Dedekind zeta $\zeta_F$, with unchanged orders, since the archimedean factor is holomorphic and nonzero there. For $|\Re z|\le\alpha$, integration by parts gives $|B(z)|\le C_n(1+|\Im z|)^{-n}$ for each $n$. Thus the entire window sum is $O(e^{\alpha R})$, including multiplicities. This bound also works for any order-bounded multiplicities on the closed window.

For the summability in that estimate, use Lemma B.1.1.2, p. 590, which bounds the **finite** Hecke $L$-function polynomially on fixed vertical strips at large height. At $2+it$ the Euler product gives $|\zeta_F(2+it)|\ge\prod_v(1+q_v^{-2})^{-1}>0$ (finite places). For $|t|>5$ the disk of radius $4$ about that point is pole-free. Jensen's inequality bounds the number of zeros in the concentric disk of radius $3$, counted by order, by $O(\log(2+|t|))$, using the strip bound on the outer disk and the lower bound at the center. The inner disk covers $0\le\Re\rho\le1$, $|\Im\rho-t|\le1$. Bounded heights give finitely many zeros by meromorphicity. Summing over unit height bands against the decay of $B$ proves the estimate without any conjecture about the zeros.

## The finite local sum detects the order of the pole

Write $L(R)$ for the displayed local side. All local restrictions vanish near the identity; identity-supported principal-value corrections are zero. At a finite place, only the shells $|g|_v=q_v^k$, $k\ge1$, contribute. On such a shell $|1-g|_v=q_v^k$, and its multiplicative mass is $\mu_v(\mathcal O_v^\times)$ even at ramified places. Thus by (B.4.4.5), p. 620, the finite contribution is exactly

$$L_f(R)=\sum_{v\text{ finite}}\sum_{k\ge1}(\log q_v)q_v^{-k/2} b(k\log q_v-R).$$

This sum is finite for each $R$. At the one complex place put $x=\log|g|_v=2\log|g|_{\rm Euc}$. In $(x,\theta)$ the multiplicative Haar is $dx\,d\theta$ by Definitions A.3.1.2 and A.3.2.2. In the off-identity local density we read the archimedean denominator on p. 519 as the normalized local modulus, as in (B.4.4.16); the subscript is absent in (12.5.1.1). The numerator is $e^{x/2}$ and the denominator is $|1-e^{x/2}e^{i\theta}|_{\rm Euc}^2$, bounded below by $(e^{x/2}-1)^2$. On the support $x\in R+\operatorname{supp}b$, this gives $L_\infty(R)=O(e^{-R/2})$ as $R\to\infty$, and a bounded integral on bounded $R$ intervals. The estimate, unlike an exact evaluation of this term, is insensitive to a fixed complex-place Haar multiplier. Even reading the denominator as an unsquared Euclidean modulus gives $O(1)$ instead, still negligible in the average below.

For $\delta>0$ apply the same linear functional to both sides:

$$\mathcal A_\delta H=\delta\int_0^\infty e^{-(1/2+\delta)R}H(R)\,dR.$$

Put $a=1/2+\delta$. Since $y=k\log q_v\ge\log 2>\sup\operatorname{supp} b$, the substitution $u=y-R$ gives $\int_0^\infty e^{-aR}b(y-R)\,dR=e^{-ay}B(a)$ with no endpoint error. Tonelli's theorem and the absolutely convergent logarithmic derivative of the Euler product give

$$\mathcal A_\delta L_f=\delta B(a)\sum_{v,k}(\log q_v)q_v^{-k(1+\delta)}=\delta B(a)\left(-\frac{\zeta_F'}{\zeta_F}\right)(1+\delta)\longrightarrow B(1/2).$$

Here only the simple pole at one is needed (Proposition 3.2.1.3 and (3.2.1.7), pp. 123–124); its residue cancels in the logarithmic derivative. In particular this does not use a prime ideal theorem or the unrestricted explicit formula. The complex place contributes zero in the limit.

On the printed global side $G(R)$, the positive polar term gives $\mathcal A_\delta[V e^{R/2}B(1/2)]=V B(1/2)$ exactly. The negative polar term and the window sum give $O(\delta)$ by their respective $O(e^{-R/2})$ and $O(e^{\alpha R})$ bounds. Hence

$$\lim_{\delta\downarrow0}\mathcal A_\delta[G-L]=(V-1)B(1/2)\ne0.$$

If the two sides agreed for all sufficiently large $R$, the difference, bounded on every bounded interval by the estimates above, would have average tending to zero. This proves the claimed failure on admissible tests.

**Consequence for the trace comparison.** The [measure comparison](trace-scalar.md#compare-the-measures-on-local-and-global-tests) does not permit setting $V=1$. With the local coefficients held fixed, a common multiplier on the printed global terms is forced to be $1/V$ by this test. This agrees with the factors in the unrestricted (B.4.4.16), p. 623. Alternatively one could retain raw global Haar and multiply the whole local side by $V$. Either change removes this particular discrepancy; neither proves that the normalized local terms minus the polar terms evaluate the same global diagonal as the restricted zero sum. That remains the operator comparison to establish. There is no conclusion here about GRH.
