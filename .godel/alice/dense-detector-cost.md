# What a unit peak costs in the dense hybrid bound

At the [fixed-window height](fixed-window-height.md), let $q$ be prime, $T=q^{1.11}$, $Q=qT$, and $X\sim(2.1\log q)^2$. We need $o(q)$ characters with a peak. The ordinary dense hybrid estimate cannot deliver this by improving the squared coefficient norm alone: Even the best witness-specific smooth polynomial pays $q^{1.055+o(1)}$ in its relaxed budget. This is a statement about the **right side of an inequality**, not a lower bound on the true mean or the number of peaks.

## Arbitrary lengths and degrees

Let $a_n$ be any finite complex sequence supported on positive $X$-smooth integers, not necessarily coefficients of a prime power polynomial. Suppose $|\sum a_n\chi(n)n^{it}|\ge1$ at one point. Put $W=\sum (Q+n)|a_n|^2$. On a fixed nonempty support $S$ the exact minimum of $W$ is

$$\left(\sum_{n\in S}\frac{1}{Q+n}\right)^{-1}.$$

Indeed $X<q$ and all phases are units; apply weighted Cauchy-Schwarz and take coefficients proportional to the conjugate phases divided by $Q+n$ for equality. Uniformly over $S$, the reciprocal mass is at most

$$\frac1{2\sqrt Q}\prod_{p\le X}(1-p^{-1/2})^{-1}\ll Q^{-1/2}q^{o(1)}.$$

Here $Q+n\ge2\sqrt{Qn}$ and the logarithm of the product is $O(\sqrt X/\log X)=o(\log q)$ by partial summation over primes. Conversely take all products of $j=\lfloor\log Q/\log X\rfloor$ distinct primes in $[X/2,X]$. They are at most $Q$, and there are $\binom mj$ of them with $m\asymp X/\log X$. Since $m/j\asymp\log q$, we have $\log\binom mj=j\log(m/j)+O(j)=(1.055+o(1))\log q$. This gives mass at least $\binom mj/(2Q)$. Hence $\inf W=q^{1.055+o(1)}$, even if the upper construction is restricted to squarefree products. It optimizes at one prescribed witness, not simultaneously at many unknown ones.

The [ordinary mean-value bound](prime-conductor-window.md) summed rather than averaged over characters charges $O(Q+N\log(2N))\sum |a_n|^2$ for support up to $N$. The displayed cost dominates $W$ up to a constant, as does the sum of these budgets on dyadic blocks. $W$ is only a relaxation; it does not supply cross-term control when recombining blocks, or persistence when turning a peak into an integral. The latter is available separately for the prime polynomial. Subpower losses in the peak normalization do not repair a fixed $.055$ deficit. In particular, merely stopping at a different product length cannot beat this budget at this fixed height.

## Can a sieve make a long completed Gram diagonal cheap?

Bob's [sieved integer Gram form](../bob/sieved-height-gram.md) works in a different height range. Consider the following attempted transfer. Complete the smooth detector by a finite nonnegative mixture of blocks $n=dj$, $P<j\le2P$, **with $P\ge Q$ in every block**. Give $j$ either weight $1$ or weight $w(j)=(\sum_{h\mid j,\,h\le z}\lambda_h)^2$, with real $|\lambda_h|\le1$, $\lambda_1=1$, and $1\le z<P$. Blocks, divisors, and weights may overlap or vary. Denote the resulting measure by $\mu(n)$, its mass on $q\nmid n$ by $C$, and its mass there on smooth indices by $S$.

Then $S\le Q^{-1/2}q^{o(1)}C$. Discard blocks with $q\mid d$, which contribute to neither mass. Every prime $P<j\le2P$ has weight one and $j>q$, so each remaining block before scaling contributes $\gg P/\log P$ coprime mass. Smoothness of $dj$ requires smoothness of $j$. Bounding $w(j)$ by the square of the divisor count gives smooth mass at most

$$\sqrt{2P}\prod_{p\le X}\sum_{r\ge0}(r+1)^2p^{-r/2}=\sqrt P\,q^{o(1)}.$$

The logarithm of a local factor is $O(p^{-1/2})$ uniformly, and the same prime sum applies. The block ratio is $\ll q^{o(1)}\log P/\sqrt P\le Q^{-1/2}q^{o(1)}$, uniformly even for $P$ much larger than $Q$. Nonnegative summation proves the claim.

For a represented unit peak, weighted Cauchy-Schwarz gives $1\le E S$, where $E=\sum_{a_n\ne0}|a_n|^2/\mu(n)$ and the detector is supported where $\mu>0$. The Gram matrix of the rows $(\sqrt{\mu(n)}\chi_i(n)n^{it_i})_n$ has every diagonal equal to $C$. Thus the ordinary dual bound on a list of unit peaks costs $E\|G\|\ge EC\ge C/S\ge q^{1.055-o(1)}$ even before estimating an off-diagonal. This rules out this positive long-quotient completion, **not** a short quotient, a different measure, or a bound exploiting the particular peak vector rather than $E\|G\|$.

## Peer comparison and an open test

In Bob's [relative-height bound (3)](../bob/relative-height-weil-list.md), $D=\log X$, $Y\sim X$, $k=\lceil K\sqrt{D\log D}\rceil$, and $L=Y^k\sum b_n^2/a^{2k}$ for threshold $a^k$. At any actual witness the degree-$k$ coefficients, even if retuned, occupy at most $\binom{\pi(Y)+k-1}{k}$ product values. Cauchy-Schwarz forces their squared norm divided by the squared threshold to be at least the reciprocal of that count. Using $\binom mk\le(em/k)^k$, $\pi(Y)\ll Y/\log Y$, and $k=o(\pi(Y))$ gives

$$\log L\ge k(\log k+\log\log Y-O(1)).$$

For the prescribed normalized positive coefficients the norm bound applies whether or not any bad twist exists: The untwisted unmodulated sum of the coefficients is one and $a<1$. Thus $\log L\asymp k\log D$ together with Bob's upper bound. Even perfect off-diagonal control in (3) leaves an unbounded prefactor; this says nothing about growth of the actual list or the [different fixed-strip argument](../bob/fixed-strip-endpoints.md).

**Next dual test, if pursued.** Shorten the powered prime sum to $k=\lfloor1.99\log q/\log X\rfloor$ for a point-sampling argument, not the integrated pair-count test. On the trimmed primes from the height note, each occupied dyadic block has scale $M=q^{1.99+o(1)}$ and coefficients at most $q^{-0.995+o(1)}$ after normalization. There are at most $\sqrt M q^{o(1)}$ smooth values per block by the same Euler product, so the squared norm is at most $q^{-0.995+o(1)}$. Each peak gives a value $\ge q^{-o(1)}$ on one of $O(\log q)$ blocks by the triangle inequality. On each common block try to bound the **signed** completed Gram operator with one arbitrary time per distinct character. A uniform bound $\|G\|\ll q^{1.995-\epsilon}$ for some fixed $0<\epsilon<.005$ would give $o(q)$ peaks by duality; its diagonal is only $O(M)$ for a bounded cutoff on a dyadic interval. Fixed-time orthogonality does not justify this for character-dependent times. Nor can one simply ask for entrywise $o(\sqrt M)$ at arbitrary allowed times. Take a smooth cutoff equal to one on $[1,2]$ and supported in $(7/8,17/8)$. For a nonprincipal ratio character modulo $q$, Poisson summation gives integrals with phases $u\log x-2\pi h x/q$ and a Gauss factor of modulus $1/\sqrt q$ for $q\nmid h$. Take the allowed time difference $u=2\pi(3M/2)/q$. Exactly $h=1$ is stationary on the support; stationary phase gives magnitude $(1+o(1))\sqrt{3M/2}$ after the Gauss factor. Repeated integration by parts in $x/M$ makes the other terms negligible since $M/q\to\infty$ and their phase derivatives have size $\gg (1+|h|)M/q$. These are admissible times, not two exhibited peaks. No such signed estimate, or [retained collision saving](rich-column-rows.md), is proved here. See the [dispatch comparison](norm-dispatch-review.md) for why the norm calculation belongs before that investigation.
