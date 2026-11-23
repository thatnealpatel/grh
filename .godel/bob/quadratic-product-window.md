# A conductor-sized Weil floor for most prime quadratic characters

Fix $A>0$. As $Q\to\infty$, outside $O_{A,\varepsilon}(Q^{1/2+\varepsilon})$ primes $Q<q\le 2Q$, the Legendre character $\chi_q=(\cdot/q)$ has Weil floor $(1+o(1))\log q$ on the window of length $D_q=2\log(A\log q)$. In particular this holds past the unsigned threshold $A=1$. The lower bound also holds on every finite Pick block with distinct real nodes $m\ge(\log\log q)^3$ and $\sum_m1/m\le D_q/2$, relative to $C_{mn}=1/(m+n)$. The exceptional set is independent of the test and the block. Here and below $\varepsilon>0$ is arbitrary but fixed. This addresses a thin family that can be entirely exceptional in an average over all characters of each prime. It does not prove the estimate for each prime or for every support of any one character.

## Large values with a time chosen separately at each prime

Let $X\sim (A\log Q)^2$ be common to all the characters, $u_p=(\log p)/\sqrt p$, $S=\sum_{p\le X}u_p\sim 2\sqrt X$, and $P_\chi(t)=\sum_{p\le X}u_p\chi(p)p^{it}$. For **any fixed** $\alpha>0$, put $Y=Q^\alpha$ and $V=\log Q/\log\log Q$. Then

$$
 \#\{Q<q\le 2Q:\ q\text{ prime},\ \sup_{|t|\le 2Y}|P_{\chi_q}(t)|>V\}
 \ll_{A,\alpha,\varepsilon} Q^{1/2+\varepsilon}. \tag{1}
$$

To see why integration in time need not spend the exceptional-set exponent, amplify a set of simultaneous large values into **distinct product conductors**. Let $R$ be the count in (1). Choose $t_j$ at each bad prime $q_j$ and phases $|z_j|=1$ with $z_jP_{\chi_{q_j}}(t_j)>V$. Write $\mathbb E_p$ for the probability with mass $u_p/S$, put $\eta=V/S$, and set $F(p)=\sum_j z_j\chi_{q_j}(p)p^{it_j}$. For an even fixed $m=2r$, Jensen gives $\mathbb E_p |F|^{2r}\ge(R\eta)^{2r}$. Expand $F^r\bar F^r$. A tuple of indices contributes, up to a constant phase, the prime average of its product character at the sum of its first $r$ times minus its last $r$. Each average has modulus at most one. Tuples repeating an index number $O_m(R^{m-1})$. Unless $R\ll_m\eta^{-m}$, at least $c_m (R\eta)^m$ ordered tuples of **distinct** indices have average of modulus $\ge\eta^m/4$: Otherwise the sum of the absolute contributions would be less than $(R\eta)^m$. Each unordered subset occurs at most $m!$ times. Its character is real primitive of conductor exactly the product of its primes by CRT, and distinct subsets have distinct conductors. Thus for $M=\lceil(2Q)^m\rceil$ there are $\gg_m(R\eta)^m$ distinct real primitive characters of conductor $\le M$ attaining $|P_\chi(t)|\ge W=S\eta^m/4$ at some $|t|\le 2mY$.

We now use only a **fixed-time** sieve. One reason not to infer the needed time estimate formally is that the general transfer in [Corrigan and Zhao, arXiv:2211.00260, §2](https://arxiv.org/abs/2211.00260) does not follow from its stated hypothesis: For a singleton primitive character Cauchy gives the admissible $\Delta(Q,N)=N$, hence their rule gives $\Delta_T=N$. At $N=2$, $a_1=1$, $a_2=0$, the time integral of $|S(it,\chi)|^2$ on an interval of length $T$ is $T$, not $O(2)$. This tests the intermediate continuous inequality, **not** the family-specific $QT+N$ bound, which has a time main term. We need neither that bound nor a verdict on it.

[Heath-Brown, *A mean value estimate for real character sums*, Acta Arith. 72 (1995), Corollary 2, p. 238](https://doi.org/10.4064/aa-72-3-235-275) gives, for all complex $a_n$ supported on $n\le N$ and every $\nu>0$,

$$
 \sum_{\chi\ {\rm real\ primitive},\ {\rm cond}(\chi)\le M}
 \left|\sum_n a_n\chi(n)\right|^2
 \ll_\nu (MN)^\nu(M+N)\sum_{ab=\square}|a_a a_b|.
$$

Take $k=\lfloor\log M/\log X\rfloor$, $N=\lfloor X^k\rfloor\le M$, and expand $P_\chi(t)^k$ with coefficients $d_n n^{it}$, $d_n\ge0$. The square-pair sum is exactly $\mathbb E(\sum_{p\le X}u_p e_p)^{2k}$ for independent uniform signs $e_p$, since odd prime multiplicities average to zero. With $\sigma^2=\sum u_p^2\ll(\log X)^2$ by partial summation, coefficientwise comparison of $\prod_p\cosh(u_p z)$ with $\exp(\sigma^2z^2/2)$ bounds this sum by $(2k)!\sigma^{2k}/(2^kk!)\le(2k\sigma^2)^k$. No squarefree-support assumption on $P^k$ is needed.

The derivative costs $|P'_\chi|\le S\log X$. A grid on $[-2mY,2mY]$ with gaps at most $W/(2S\log X)$ captures every large value at height $W/2$, using $O_m(1+Y S\log X/W)=Q^{\alpha+o(1)}$ points. At each point the moment ratio is

$$
 \left(\frac{2k\sigma^2}{(W/2)^2}\right)^k
 \le \exp\{k[-\log\log Q+O_m(\log\log\log Q)+O_A(1)]\}
 = Q^{-m/2+o(1)}\quad\text{as an upper bound}.
$$

Indeed $W\asymp_{A,m}\log Q/(\log\log Q)^m$ and $k\sim m\log Q/(2\log\log Q)$. Summing the sieve over the grid bounds the count of product characters by $Q^{m/2+\alpha+2m\nu+o(1)}$. Taking the $m$-th root gives $R\le Q^{1/2+\alpha/m+2\nu+o(1)}$, including the discarded polylogarithmic case. Choose the even $m$ large in terms of $\alpha,\varepsilon$, then $\nu$ small. This proves (1) without invoking a hybrid short-interval quadratic large sieve.

## Prime cost at a specified archimedean energy

Use one cutoff for both assertions, $X=(A\log(2Q))^2\exp((\log\log Q)^{-1/2})$. It includes all active shifts for each compact test. Let $B$ be the sum of the two signed translations by $\pm\log n$ with coefficients $\Lambda(n)\chi_q(n)/\sqrt n$ up to $X$. Its multiplier has modulus at most $2V+O(\log X)$ for $|t|\le Y$ on the good set of (1): Squares cost $O(\log X)$, and exponents at least three cost $O(1)$. On the whole line its modulus is at most $H=2\sum_{n\le X}\Lambda(n)/\sqrt n=(4A+o(1))\log q$ by PNT. The factor four is affordable because (1) permits arbitrarily large **fixed** $\alpha$.

For a unit test $h$, write $d\mu_h=|\widehat h(t)|^2dt/(2\pi)$, $G(h)=\int g_a(t)d\mu_h(t)$, where $g_a(t)=\Re\psi(1/4+a/2+it/2)-\log\pi$ in parity $a$. Take an absolute $C$ with $g_a(t)+C\ge\log(2+|t|)$ in both parities. The exact Fourier split of the already truncated operator gives the explicit tail charge

$$
 |\langle Bh,h\rangle|\le 2V+O(\log X)+H\mu_h(|t|>Y)
 \le 2V+O(\log X)+\frac{H}{\log(2+Y)}[G(h)+C]. \tag{2}
$$

There is no convolution or support-leakage error in (2): Neither frequency piece is treated as a new compact test. In particular $G(h)=o(\log q)$ gives signed prime cost $o(\log q)$ for the **same** test. Choose $\alpha>4A$, so the coefficient of $G+C$ is less than one eventually. Subtracting (2) from $\log q+G(h)$ gives floor at least $\log q-2V-O(\log X)-C$. A fixed smooth unit test on an interval shorter than $\log 2$ has no prime terms and $G=O(1)$, giving the stated leading equality on windows.

For a normalized exponential polynomial for one of the stated blocks, (2) applies unchanged to its zero extension with finite Gamma energy. Its extra, untruncated shifts above $X$ cost $o(1)$ uniformly: With $b=D_q/2$, $B_0=\log\log q$, and $s=B_0^2$, the [block tail bound, §4](../adhoc/prime-translation-norm.md) gives $|A_h(t)|\le e^{J-st}$ for the autocorrelation at $t\ge0$, with $J/s\le 2b+O(1/B_0)$. Thus their cost is at most $2e^{J-(s-2)\log X}\sum_n\Lambda(n)n^{-5/2}=o(1)$, since $\log X\ge 2b+B_0^{-1/2}$. The [block form identity](../adhoc/pick-block-weil-window.md) now gives the lower bound relative to $C$. No rank bound or recovery rate is assumed.

**Next decision.** The amplification uses independent conductor factors, not merely a supply of characters: At a single modulus, collisions of the product characters invalidate the $\gg (R\eta)^m$ count. For each-prime results, bound those collisions together with the signed time sums, or seek a different test-specific argument. For every quadratic conductor even the [unmodulated endpoint mass](endpoint-arithmetic-test.md) remains a necessary arithmetic obligation.

**After Work:** The [growing-window calculation](growing-quadratic-window.md) keeps the same exceptional exponent and all tests for $1\le A(Q)=o(\log\log Q)$ by varying the sieve threshold with the Gamma cost. Do not repeat the fixed-order estimate with $A(Q)$ substituted for a constant. To go beyond this scale on average, test the product threshold at intermediate heights first. This does not remove the every-prime endpoint obligation.
