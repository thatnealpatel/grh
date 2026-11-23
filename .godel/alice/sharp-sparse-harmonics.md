# Sharp angular budget for any number of sparse queries

For $s\in\mathbb R/(2\pi\mathbb Z)$ let $f(s)=|\sin(s/2)|$, and write $C_N=1/[N\sin(\pi/(2N))]$. For **every** integer $N\ge1$,

$$
\inf_{J\subset\mathbb Z_{>0},\ |J|\le N-1}\ \sup_{\mu:\ \widehat\mu(j)=0\ (j\in J)}\int f\,d\mu=C_N,
$$

where $\mu$ ranges over circle probability laws and the moments are complex. Thus taking the first $N-1$ modes minimizes the worst possible mean. There is no bound on the largest competing index. Under $s=2v-\pi$ the mean is that of $|\cos v|$, and a zero at $j$ is a zero at $2j$ in $v$; every law in $s$ can be lifted by taking $v=(s+\pi)/2$ on representatives. This sharpens the [single-missing-mode bound](sparse-harmonic-budget.md) and the [40-query threshold certificate](../bob/exact-sparse-harmonic-count.md). We use Bob's shifted grids, but charge a high query to just one missing divisor rather than bounding its size at a fixed threshold.

**Choose a grid.** Given $J$, let $M=\{1,\ldots,N\}\setminus J$. There are at most $|M|-1$ queries above $N$. Assign each such query $j$ to the **largest** $n\in M$ dividing $j$, if one exists. Choose an unassigned $n\in M$. If $n\le 3N/4$, use density $1-\cos(ns)$ against normalized arc length. Its queried moments vanish, and by the cosine coefficient of $f$ its mean is $(2/\pi)/(1-1/(4n^2))$. This exceeds $C_N=(2/\pi)/\operatorname{sinc}(\pi/(2N))$: Indeed $\operatorname{sinc}(z)=\sin(z)/z\ge1-z^2/6$ for $0<z\le\pi/2$, and $1/(4n^2)\ge4/(9N^2)>\pi^2/(24N^2)$.

Now $n>3N/4$. The uniform law on $(2l+1)\pi/n$, $0\le l<n$, has mean $C_n$ and kills all modes not divisible by $n$ (finite geometric sums). All queried multiples of $n$ exceed $N$, since $n\notin J$ and $2n>N$. If $n=N$, none exist by nonassignment, so this grid already gives $C_N$. For $n<N$, each queried multiple $j=kn$ is assigned to some $n'>n$ in $M$. Thus

$$
k\ge\frac{n'}{\gcd(n,n')}\ge 1+\frac{n}{N-n},
$$

since $\gcd(n,n')\le n'-n\le N-n$. This restricts **all** queries that disturb this grid, even ones that disturb many other grids.

**Pay for the shifts.** Add to the grid point an independent symmetric shift $\pm\pi/(2j)$ for each $j\in J$ divisible by $n$. Convolution preserves all previously vanishing moments and kills every such $j$. Write $\delta$ for the sum of shifts. On the real lift of each grid node $s_l$, $f(s_l+\delta)\ge\sin((s_l+\delta)/2)$, even when a node wraps. By symmetry and independence the new mean is at least $C_n\prod_{n\mid j,\ j\in J}\cos(\pi/(4j))$. The fractional loss in this lower bound is at most

$$
\frac{\pi^2}{32}\sum_{n\mid j,\ j\in J}\frac1{j^2}
\le \frac{\pi^2}{32 n^2}\,\frac{N-n}{n}.
$$

Here $1-\prod a_j\le\sum(1-a_j)$ for $a_j\in[0,1]$, and $1-\cos u\le u^2/2$. The sum over distinct $k=j/n$ is bounded by the integral of $t^{-2}$ from $\lceil1+n/(N-n)\rceil-1$ to infinity.

Put $x=n/N$, $w=\pi/(2n)$, $z=\pi/(2N)$. The fractional grid advantage over the target satisfies

$$
1-C_N/C_n\ge \operatorname{sinc}(z)-\operatorname{sinc}(w)
=\int_0^1\int_z^w t\sin(tu)\,du\,dt
\ge\frac{w^2-z^2}{3\pi}=\frac{\pi}{12n^2}(1-x^2).
$$

The first inequality divides the positive difference by $\operatorname{sinc}(z)\le1$; the last uses $\sin v\ge 2v/\pi$ on $[0,\pi/2]$. The loss divided by this lower bound is at most $3\pi/[8x(1+x)]<2\pi/7<1$ for $3/4<x<1$. Hence even the shifted grid exceeds $C_N$ in this case. This proves the lower bound for every $J$, including $J=\varnothing$. Conversely the [consecutive Hermite majorant](../bob/initial-harmonic-budget.md#a-sharp-constant-for-degree-less-than-n) has constant $C_N$ and degree $<N$ (use $1$ when $N=1$). Its integral against any law with the first $N-1$ moments zero is exactly its constant, so it proves the upper bound for that choice of queries.

**Consequence and scope.** At any angular ceiling $2/\pi+b$, $b>0$, the least number of exact zero-moment queries that suffice for a non-strict ceiling is $\min\{N-1:C_N\le 2/\pi+b\}$. The leading constant as $b\downarrow0$ is $\sqrt{\pi/12}$ in units of $b^{-1/2}$, by the sine expansion. A deterministic adaptive choice on the uniform law's all-zero answer path faces the same lower bound. This neither asserts uniqueness of the optimal set nor controls noisy moments, prime phases, the Gamma margin, or zeta packets. It is an obstruction to saving harmonics in this angular comparison, not an estimate for the large-$S$ smooth rectangles.
