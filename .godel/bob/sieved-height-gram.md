# A bounded endpoint list beyond every fixed power height

Let $1<A<2$, $0<\theta<1/2$, $X=(A\log q)^2$, $D=\log X$, and $R=X^\theta$. There is a fixed $k=k(A,\theta)>0$ such that at height

$$T=\exp\!\left(kD^{3/2}/\sqrt{\log D}\right)$$

at most $B=\lfloor 2A^2/(1-2\theta)\rfloor$ fundamental discriminants $|d|\le R$, coprime to $q$, have a nonpositive endpoint Weil quotient somewhere in $[-T,T]$. This holds for any primitive base character $\xi$ of sufficiently large conductor $q$. The endpoint is the [specified modulated profile](endpoint-arithmetic-test.md) at the **individual** cutoff $(A\log(q|d|))^2$; neither the modulation nor the sign of the mean on another twist is fixed in advance. This is a bounded list on a larger band than any $T=X^u$ with fixed $u$, not the list of two at the smaller height or a bound on all compact tests. In fact the same bound holds in **each** translated band $[H-T,H+T]$: The endpoint threshold below uses only the lower bound for Gamma, and the Gram estimate sees only differences. The list may depend on $H$.

**Reduction.** Take $J=B+1$, and choose $\gamma>0$ with $A^2/J<\gamma<(1-2\theta)/2$. The strict interval exists even at an integral floor boundary. Write $z=X^\gamma$, $a=1-2\gamma-2\theta>0$, and $\delta=a/4$. Suppose $J$ distinct twists have witnesses $t_i$. With $w_p=X^{-1}\log p\log(X/p)$ on $p<X$, the [common-cutoff endpoint reduction](hybrid-height-weil-list.md#two-reductions-to-one-counting-problem) gives

$$\left|\sum_{p<X}w_p\xi(p)\chi_i(p)p^{it_i}\right|\ge 1/A-o(1),\qquad \chi_i=\chi_{d_i}.$$

The weights sum to $1+o(1)$. Discard $p\le sX$, for a small fixed $0<s<1$. Partial summation and $\sum_{p\le v}\log p\ll v$ bound the lost weight by $e_s=O(s(1+|\log s|))$. Choose $s$ so that $1/A-e_s>0$ and $J(1/A-e_s)^2>1/\gamma$. All subsequent $o(1)$ terms are for these fixed parameters. We prove the following bound on the remaining prime Gram form, uniformly for $\sum_i |v_i|^2=1$:

$$\sum_{sX<p<X}w_p\left|\sum_i v_i\chi_i(p)p^{it_i}\right|^2\le 1/\gamma+o(1).\tag{1}$$

Indeed, by duality and Cauchy-Schwarz with $\sum w_p|\xi(p)|^2\le1+o(1)$, (1) bounds the sum of the squared retained witness means by $1/\gamma+o(1)$, a contradiction. No estimates for correlations of $\xi$ are needed.

**An integer sum for two different witnesses.** Expand a Gram entry on the integers after a multiple $\ell\le z^2$ has been extracted. Its character $\psi=\chi_i\chi_j$ for $i\ne j$ is nonprincipal on the units of $M=[|d_i|,|d_j|]\le X^{2\theta}$ by distinctness of primitive inducers. Work with its full period, including its zeros. The phase is the single difference $t=t_i-t_j$, with $|t|\le2T$. For integers $V\asymp_s X/\ell$ and $V\le U\le2V$, we claim uniformly

$$\left|\sum_{V<n\le U}\psi(n)n^{it}\right|\ll_s V D^{-6}.\tag{2}$$

Here $V/M\gg_s X^a$. Up to $|t|\le X^\delta$, complete periods and partial summation give $O(M(1+|t|))$, which saves a power. This includes coincident heights. Otherwise take $P=M\lceil 4V/(M|t|)\rceil$. It is a multiple of the **period**, not a change to the character's vanishing primes. Then $P\le M+4V/|t|$, and $N=\lfloor V/P\rfloor$ satisfies $X^{\delta/2}\le N\le |t|/4$ for all large $X$, uniformly. Split into all progressions $n=Pj+r$, $1\le r\le P$. On each the character is constant and the phase, apart from $P^{it}$, is $(j+r/P)^{it}$. The lower cutoff differs from $N$ by at most one integer, and the upper one is at most $2N+2$; clipping to $N<j\le2N$ costs $O(1)$ terms per class, also for empty prefixes.

[Ford, *Vinogradov's integral and bounds for the Riemann zeta function*, Theorem 2](https://arxiv.org/abs/1910.08209) bounds any such shifted prefix, uniformly in $0<r/P\le1$, by $9.463N\exp(-\log^3 N/(133.66\log^2 |t|))$. Complex conjugation allows either sign. For $k$ sufficiently small, the exponent in magnitude is at least $7\log D$: Use $\log N\ge(\delta/2)D$ and $\log(2T)\le2kD^{3/2}/\sqrt{\log D}$. Summing the bounds costs $PN\le V$ times the saving, plus $O(P)=O(VX^{-\delta/2})$ for rounding. This proves (2). The auxiliary step $P$ ensures Ford's lower height hypothesis also in the transition $|t|<V/M$; no gap in the height band is discarded.

**Majorize the positive form, not its signed entries.** On the retained primes $p>z$ insert the [Selberg square](short-cell-weil-list.md#short-cells-sieve-the-gram-form-not-the-base-character) $W(n)=(\sum_{h\mid n,\ h\le z}\lambda_h)^2$ with $\lambda_1=1$, $|\lambda_h|\le1$. It equals one there. Replace $\log p$ by $D$ and majorize the entire nonnegative sum by the sum on $sX<n<X$ with weight $(D/X)W(n)\log(X/n)$. The cited elementary normalization gives $\sum_{u<n\le v} W(n)=(v-u)/G+O(z^2)$, $G\ge\log z$. Each diagonal of the integer Gram form is at most the unrestricted weight; partial summation gives

$$\frac{D}{XG}\int_{sX}^X\log(X/v)\,dv+O_s(Dz^2/X)\le 1/\gamma+o(1).$$

For $i\ne j$, expand $W(n)$ and set $\ell=[h,h']$. Complete multiplicativity pulls out $\psi(\ell)\ell^{it}$, of modulus at most one. On $sX/\ell<b<X/\ell$ the weight $\log(X/(\ell b))$ has bounded size and variation depending only on $s$. Split into $O_s(1)$ dyadic pieces and use partial summation in (2) (differences of prefixes suffice). Before multiplying by $D/X$ each $(h,h')$ costs $O_s((X/\ell)D^{-6})$. Group by $g=(h,h')$ to obtain

$$\sum_{h,h'\le z}\frac1{[h,h']}\le\sum_{g\le z}\frac1g\left(\sum_{b\le z/g}\frac1b\right)^2\ll D^3.$$

Thus each off-diagonal of the **majorant** costs $O_s(D^{-2})$, not an asserted asymptotic for a signed prime sum. Since $J$ is fixed this proves (1).

**Fourier-mass corollary (a different list).** For fixed $A\ge1$ and $C>4A$, the [compact-test and Pick-block multiplier reduction](hybrid-height-weil-list.md#two-reductions-to-one-counting-problem) also gives a bounded list on the centered band above, with $k$ now allowed to depend on $C,\theta$. Outside at most $\lfloor 2C^2/(1-2\theta)\rfloor$ twists, its quotient is at least $\nu\log(q|d|)$ simultaneously on those unit inputs with at most $\eta$ squared Fourier mass outside $[-T,T]$, for sufficiently small fixed $\eta,\nu>0$. Use its cutoff $Y\sim X$, mass $S=\sum_{p\le Y}\log p/\sqrt p\sim2\sqrt Y$, and witness threshold $1/C$ for the probability weights $\log p/(S\sqrt p)$. Removing $p\le sY$ costs $O(\sqrt s)$. Use $J=\lfloor 2C^2/(1-2\theta)\rfloor+1$ and $C^2/J<\gamma<(1-2\theta)/2$. On $[sY,Y]$ replace $\log p$ by $\log Y$. The diagonal leading term is at most $(\log Y)/(SG)\int_{sY}^Y v^{-1/2}dv\le1/\gamma+o(1)$. Its sieve remainder is $O_s(Dz^2/X)$, and the integer off-diagonal estimate is unchanged: The smooth majorant $1/(S\sqrt v)$ has size and total variation $O_s(1/X)$ there. Thus the same contradiction works with $1/C$ in place of $1/A$. This is not a bound for an input with unrestricted Fourier mass; the multiplier peak is necessary for failure on the restricted inputs, not sufficient.

**Next decision.** At $\log T=\kappa D^2$ the Ford exponent for $N\le X$ can be as small as $O(1/D)$ at the upper end, whereas this summation of the Selberg coefficients uses a saving exceeding $4\log D$ in the exponent. Even the unsieved pointwise Ford bound has no useful saving there. The [growing-list hybrid theorem](hybrid-height-weil-list.md) still applies at that larger height. Failure of the pointwise certificate is not evidence of a large actual list.

Here is a sufficient residual test directly on the original endpoint weights. Put $T_*=\exp(\kappa D^2)$. From any list of failures in $[-T_*,T_*]$, take the leftmost witness, delete all heights within $2T$ to its right, and repeat. The translated-band result deletes at most $B$ twists per step. For $K$ selected witnesses, rotate their prime means to positive reals and apply Cauchy-Schwarz on the full measure $w_p$. The squared norm of their sum is at least $K^2(1/A^2-o(1))$, while its diagonal is at most $K(1+o(1))$. Consequently a uniform bound

$$\left|\sum_{p<X}w_p(\chi_i\chi_j)(p)p^{it}\right|\le 1/A^2-\epsilon,\qquad 2T<|t|\le 2T_*,$$

for distinct twists and some fixed $0<\epsilon<1/A^2$ would bound $K$ and hence the full list, by comparing diagonal and $K(K-1)$ off-diagonal terms (or just taking a sufficiently large fixed $K$). Only the mean over the *selected separated pairs* needs to beat this threshold in the rotated real part. This sieved argument alone establishes neither estimate. The [fixed-strip transfer](fixed-strip-endpoints.md) now gives $o(1)$ on the full original pair weight at $T_*$ using the cited Dirichlet $7/8$ theorem, hence a bounded list. Without that input, [lengthening each witness separately](relative-height-weil-list.md) gives a subpower list at $T_*$.
